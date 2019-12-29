------------------------------- MODULE benor -------------------------------
\* Advait Deshmukh; UBIT Name - advaitpr
\* Dipannita Adhikary; UBIT Name - adhikary

(*\* Ben-Or algorithm *)
EXTENDS Integers, Sequences, FiniteSets
\* N - Number of nodes; F - Number of failures; MAXROUND - Total rounds to run
CONSTANT N, F, MAXROUND, INPUT
ASSUME N \in Nat /\ F < N
Procs == 1..N
Rounds == 1..MAXROUND

(* 
 --algorithm BenOr
 { 
    variable p1Msg = {}, p2Msg = {}; \* Message boards for Phase1 and Phase2
    define
    {
        SentP1Msg(r) == {m \in p1Msg: (m.round=r)}                              \* Message in the Phase 1
        SentP1MsgValue(r,b) == {m \in p1Msg: (m.round = r) /\ (m.val=b)}        \* Corresponding value for that message
        
        SentP2Msg(r) == {m \in p2Msg: (m.round = r)}                            \* Message in the Phase 2
        SentP2MsgValue(r,b) == {m \in p2Msg: (m.round = r) /\ (m.val = b)}      \* Corresponding value for that message
     }
     
     macro SendPhase1Msg(n,r,b) 
     {
        p1Msg := p1Msg \union {[node_id |-> n, round |-> r, val |-> b]};        \* Format of the message - NodeId, Round and the Value
     }
          
     macro ReceivePhase1Msg(n,r) 
     {
        await (Cardinality(SentP1Msg(r)) >= (N-F));                             \* Collect messages from other nodes and wait till the number of Phase 1 messages is greater than (N-F)
        if (Cardinality(SentP1MsgValue(r,1))*2 > (N))                           \* From the received messages check other's values for any majority
        {
            p2val := 1;     \* One Majority for that round
        }
        else if(Cardinality(SentP1MsgValue(r,0))*2 > (N))
        {
            p2val := 0;     \* Zero Majority
        }
        else
        {
            p2val := -1;    \* No majority of 0 or 1
        };
        p1c := TRUE         \* Boolean flag for checking within fair process section of the algorithm 
     }
     
     macro SendPhase2Msg(n,r,b)
     {
            p2Msg := p2Msg \union {[node_id |-> n, round |-> r, val |-> b]};
     }
     
     macro ReceivePhase2Msg(n,r)
     {
        await (Cardinality(SentP2Msg(r)) >= (N-F));
        if (Cardinality(SentP2MsgValue(r,0)) >= (F + 1)){
            val := 0;           \* Decide/Agree on 0 because of its majority
        }
        else if(Cardinality(SentP2MsgValue(r,1)) >= (F + 1)){
            val := 1;           \* Decide/Agree on 1 because of its majority
        };
     }
     
     macro DecideNextRoundVal(n,r)
     {
        if (SentP2MsgValue(r,1) # {}){                              \* Choose 1 for next round if 1 was sent in the Phase 2
            p1val := 1;
        }else if(SentP2MsgValue(r,0) # {}){                 
            p1val := 0;                                             \* Choose 0 for next round if 0 was sent in the Phase 2
        }
        else{
            with (rval \in {0,1})                                   \* Random choice between 0 and 1s
                p1val := rval
        };
     }
   
   \* Main Node Process
   fair process (p \in Procs)
   variable node_id = self, r = 0, p1val = INPUT[self], p2val = -1, decided = -1, val = -1, p1c = FALSE;
   {
        P: while (r < MAXROUND) {
            r := r + 1;
            
            P1 : SendPhase1Msg(node_id, r, p1val);                  \* Send message to other nodes for phase 1
            CP1 : ReceivePhase1Msg(node_id, r);                     \* collect messages from other nodes for phase 1
            if (p1c = TRUE){
                    P2: SendPhase2Msg(node_id, r, p2val);           \* if phase 1 is done, send message to other nodes for phase 2
                    CP2: ReceivePhase2Msg(node_id, r);              \* collect messages from other nodes for phase 2
                    };
            D: if (val \in {0, 1}){
                    decided := val  \* decide upon a value only if it's 0 or 1
                };
         
                 DecideNextRoundVal(node_id, r);
     }
   }  
 }              
 
*)
\* BEGIN TRANSLATION
VARIABLES p1Msg, p2Msg, pc

(* define statement *)
SentP1Msg(r) == {m \in p1Msg: (m.round=r)}
SentP1MsgValue(r,b) == {m \in p1Msg: (m.round = r) /\ (m.val=b)}

SentP2Msg(r) == {m \in p2Msg: (m.round = r)}
SentP2MsgValue(r,b) == {m \in p2Msg: (m.round = r) /\ (m.val = b)}

VARIABLES node_id, r, p1val, p2val, decided, val, p1c

vars == << p1Msg, p2Msg, pc, node_id, r, p1val, p2val, decided, val, p1c >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ p1Msg = {}
        /\ p2Msg = {}
        (* Process p *)
        /\ node_id = [self \in Procs |-> self]
        /\ r = [self \in Procs |-> 0]
        /\ p1val = [self \in Procs |-> INPUT[self]]
        /\ p2val = [self \in Procs |-> -1]
        /\ decided = [self \in Procs |-> -1]
        /\ val = [self \in Procs |-> -1]
        /\ p1c = [self \in Procs |-> FALSE]
        /\ pc = [self \in ProcSet |-> "P"]

P(self) == /\ pc[self] = "P"
           /\ IF r[self] < MAXROUND
                 THEN /\ r' = [r EXCEPT ![self] = r[self] + 1]
                      /\ pc' = [pc EXCEPT ![self] = "P1"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ r' = r
           /\ UNCHANGED << p1Msg, p2Msg, node_id, p1val, p2val, decided, val, 
                           p1c >>

P1(self) == /\ pc[self] = "P1"
            /\ p1Msg' = (p1Msg \union {[node_id |-> node_id[self], round |-> r[self], val |-> p1val[self]]})
            /\ pc' = [pc EXCEPT ![self] = "CP1"]
            /\ UNCHANGED << p2Msg, node_id, r, p1val, p2val, decided, val, p1c >>

CP1(self) == /\ pc[self] = "CP1"
             /\ (Cardinality(SentP1Msg(r[self])) >= (N-F))
             /\ IF Cardinality(SentP1MsgValue(r[self],1))*2 > (N)
                   THEN /\ p2val' = [p2val EXCEPT ![self] = 1]
                   ELSE /\ IF Cardinality(SentP1MsgValue(r[self],0))*2 > (N)
                              THEN /\ p2val' = [p2val EXCEPT ![self] = 0]
                              ELSE /\ p2val' = [p2val EXCEPT ![self] = -1]
             /\ p1c' = [p1c EXCEPT ![self] = TRUE]
             /\ IF p1c'[self] = TRUE
                   THEN /\ pc' = [pc EXCEPT ![self] = "P2"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "D"]
             /\ UNCHANGED << p1Msg, p2Msg, node_id, r, p1val, decided, val >>

P2(self) == /\ pc[self] = "P2"
            /\ p2Msg' = (p2Msg \union {[node_id |-> node_id[self], round |-> r[self], val |-> p2val[self]]})
            /\ pc' = [pc EXCEPT ![self] = "CP2"]
            /\ UNCHANGED << p1Msg, node_id, r, p1val, p2val, decided, val, p1c >>

CP2(self) == /\ pc[self] = "CP2"
             /\ (Cardinality(SentP2Msg(r[self])) >= (N-F))
             /\ IF Cardinality(SentP2MsgValue(r[self],0)) >= (F + 1)
                   THEN /\ val' = [val EXCEPT ![self] = 0]
                   ELSE /\ IF Cardinality(SentP2MsgValue(r[self],1)) >= (F + 1)
                              THEN /\ val' = [val EXCEPT ![self] = 1]
                              ELSE /\ TRUE
                                   /\ val' = val
             /\ pc' = [pc EXCEPT ![self] = "D"]
             /\ UNCHANGED << p1Msg, p2Msg, node_id, r, p1val, p2val, decided, 
                             p1c >>

D(self) == /\ pc[self] = "D"
           /\ IF val[self] \in {0, 1}
                 THEN /\ decided' = [decided EXCEPT ![self] = val[self]]
                 ELSE /\ TRUE
                      /\ UNCHANGED decided
           /\ IF SentP2MsgValue(r[self],1) # {}
                 THEN /\ p1val' = [p1val EXCEPT ![self] = 1]
                 ELSE /\ IF SentP2MsgValue(r[self],0) # {}
                            THEN /\ p1val' = [p1val EXCEPT ![self] = 0]
                            ELSE /\ \E rval \in {0,1}:
                                      p1val' = [p1val EXCEPT ![self] = rval]
           /\ pc' = [pc EXCEPT ![self] = "P"]
           /\ UNCHANGED << p1Msg, p2Msg, node_id, r, p2val, val, p1c >>

p(self) == P(self) \/ P1(self) \/ CP1(self) \/ P2(self) \/ CP2(self)
              \/ D(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Procs: p(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(p(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

\* Agreement is done only when the decided values same and are 0 or 1
Agreement == (\A j,k \in Procs: (decided[j] \in {0,1}) /\ (decided[k] \in {0,1}) => decided[j]=decided[k])

\* Progress is not violated when decided values are 0 or 1 and a majority is reached
Progress ==  <>(\A q \in Procs: decided[q] # -1)


\* We check if number of 1s equals number of 0s in Phase 2 of a round for no majority and if all the decided values are -1
BaitProgress == \A q \in Procs: \A x \in Rounds: Cardinality(SentP2MsgValue(x, 0)) = Cardinality(SentP2MsgValue(x, 1)) => decided[q] = -1
\* onecount ==  \A z \in Procs: \A y \in Rounds: Cardinality(SentP2MsgValue(y, 1))
\*BaitProgress == (zerocount => \A hello \in Procs: decided[hello] = -1)


\* We need to check if 0 or 1 is in the minority and accordingly we check if the minority property is being  violated or not by checking if values in minority are decided or not 
MinorityZero == \A q \in Procs: \A x \in Rounds: Cardinality(SentP2MsgValue(x, 0)) < Cardinality(SentP2MsgValue(x, 1)) => decided[q] # 0 
MinorityOne == \A q \in Procs: \A x \in Rounds: Cardinality(SentP2MsgValue(x, 1)) < Cardinality(SentP2MsgValue(x, 0)) => decided[q] # 1
MinorityReport == (MinorityZero /\ MinorityOne)

=============================================================================
\*
(* 
Project Report - BenOr

BenOr algorithm was proposed by Dr. Michael Ben-Or in January 1983. It is intended to solve the problem of reaching consensus among N asynchronous processes.
This algorithm is intended to solve consensus problems using nondeterministic (random) binary consensus.
Consensus is achieved via a majority of decisions among N processes that are able communicate with each other using Messages. 

We initialize messageboards as p1Msg and p2Msg initialize the message with the message values as sentP1Msg/SentP2Msg and SentP1MsgValue/SentP2MsgValue respectively.
For each sent message there's a Node ID, Round Number and Value associated with it.
The messages recieved have to be greater than N-F (as majority doesn't need all values from all processes) in the first round for the node to check for majority.
If there is a majority, that is more than N/2 nodes send same values between 0 and 1, the receiving process.
If not then it sends -1 for the second round, and decision is taken if there was a majority in either 1 or 0 for all the messages sent by processes in first phase.
If consensus is not reached, the nodes that sent -1 randomly choose between 0 and 1 and this cycle continues for subsequent rounds till consensus is reached.
Thus, for the first round there wouldn't be any non determinism as we choose the random value at its end for the next round.
While this can go on forever in a production level scenario, we limit the number of rounds as per the limited capacity of our machines and check if the invariants Agreement, Bait Progress and Minority Report are satisfied or not along with the Progress property.

The key part of this algorithm is the choosing of values for next round, because it makes sure that the node only changes its proposal randomly if -1 was sent and if it wasn't, it holds on to its proposal.
This makes sure that the number of rounds that the algorithm runs to solve consensus stays the least.

Agreement:
Agreement states that all nodes agree upon the same value. We have found out that this always holds irrespective of the input.
Whenever a consensus is reached, we found out that all the nodes have decided upon the same value.
We kept F to be 3 and number of processes to be 4, and Agreement was still satisfied and the model checker did not find any violations.

Progress:
Progress states that eventually all processes will decide on a value and reach consensus and in our case, the processes will decide on a value that isn't -1.
We found out that Progress is satisfied for all conditions except for the ones where the number of 1s and 0s were equal in even number of nodes.
For eg. when input was <<0,0,1,1>> with no failures, the model checker started stuttering within the same states.
The eventuality of this property makes it special as the number of rounds increases, the likelihood of the model checker finding that progress is satisfied increases.
However, the chance of it being stuck within the same state space also increases.

Bait Progress:
Bait Progress checks for cases where consensus cannot be reached within the given number of rounds.
That is, there will be cases where all the processes will not be able to decide on a value and eventually every process decided upon -1.
We check if the number of processes with 0 proposed and number of processes with 1 proposed in the same round is equal.
In these cases majority wasn't there and even with the eventuality, progress could not be achieved.
This led to decided values being -1 for those processes and within the explored state space, the model checker also found that progress was violated.

Minority Report:
This is a safety property and it claims that if a value is in the minority, it won't be the decided value and consensus truly works.
While it is given for just zero, we have implemented it for 0 as well as for 1, to check that if 1 is in the minority, it won't be the decided value.
We check if the number of messages sent in the Phase 2 with value 0 comes in the minority or value 1 comes in the minority and see that the decided value for that process is not the minority value.
This can be seen in decided[q] # 0 and decided[q] # 1 after the implication part. In the end, we use the AND operator to be absolutely sure that MinorityReport works.
We have observed that this holds when Failures are 0.
When the number of failures increase with F=1 or F=2, the chances of violations increases as the chances of there being a minority reduces.
We got violations with Input <<0, 1, 1, 1>> and F=1 and F=2 because with failed nodes the model checker encountered states where minority was violated and 0 was chosen as the decided value.

*)
\* Modification History
\* Last modified Sun Dec 01 23:36:05 EST 2019 by Dell
\* Created Mon Nov 18 20:29:20 EST 2019 by Dell
