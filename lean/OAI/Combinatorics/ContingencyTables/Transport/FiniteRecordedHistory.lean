import OAI.Combinatorics.ContingencyTables.Machines.FiniteEncodedHistory
import OAI.Combinatorics.ContingencyTables.Counting.CompanionPhaseTrajectory

namespace OAI

/-! # The fixed-capacity recorder stores the chronological word history -/

namespace ContingencyTables.FiniteObservableTransport

open CommonBasesFPRAS FirstSuccess RealKernelApproximation
open CompanionBooleanPhase CompanionPhaseTrajectory

lemma traceStates_snoc {X U : Type*} (F : X → U → X) (us : List U) (c : X) (u : U) :
    traceStates F c (us++[u])=
      traceStates F c us++[F (us.foldl F c) u] := by
  induction us generalizing c with
  | nil => rfl
  | cons a us ih =>
    change c::traceStates F (F c a) (us++[u])=
      c::(traceStates F (F c a) us++[F (us.foldl F (F c a)) u])
    rw [ih]

def recorded {X : Type*} {k : ℕ} (F : X → (Fin k → Bool) → X) (N : ℕ) (c : X)
    (n : ℕ) (words : Fin n → Fin k → Bool) : PathState X N :=
  wordWalk (fun a bits => pathPut a (F (pathRead a) bits)) (pathInitial N c) n words

lemma recorded_position {X : Type*} {k : ℕ} (F : X → (Fin k → Bool) → X)
    (N : ℕ) (c : X) (n : ℕ) (hn : n ≤ N) (words : Fin n → Fin k → Bool) :
    (recorded F N c n words).1.val=n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (pathPut (recorded F N c n (Fin.init words))
      (F (pathRead (recorded F N c n (Fin.init words))) (words (Fin.last n)))).1.val=n+1
    rw [position_put]
    · rw [ih (by omega)]
    · rw [ih (by omega)]
      omega

lemma recorded_read {X : Type*} {k : ℕ} (F : X → (Fin k → Bool) → X)
    (N : ℕ) (c : X) (n : ℕ) (words : Fin n → Fin k → Bool) :
    pathRead (recorded F N c n words)=(List.ofFn words).foldl F c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change pathRead (pathPut (recorded F N c n (Fin.init words))
      (F (pathRead (recorded F N c n (Fin.init words))) (words (Fin.last n))))=_
    rw [read_put,ih,List.ofFn_succ',List.concat_eq_append,List.foldl_append]
    rfl

theorem recorded_prefix {X : Type*} {k : ℕ} (F : X → (Fin k → Bool) → X)
    (N : ℕ) (c : X) (n : ℕ) (hn : n ≤ N) (words : Fin n → Fin k → Bool) :
    historyPrefix (recorded F N c n words)=traceStates F c (List.ofFn words) := by
  induction n with
  | zero => exact prefix_initial N c
  | succ n ih =>
    change historyPrefix (pathPut (recorded F N c n (Fin.init words))
      (F (pathRead (recorded F N c n (Fin.init words))) (words (Fin.last n))))=_
    rw [prefix_put]
    · rw [ih (by omega),recorded_read,List.ofFn_succ',List.concat_eq_append,traceStates_snoc]
      rfl
    · rw [recorded_position F N c n (by omega)]
      omega

end ContingencyTables.FiniteObservableTransport

end OAI
