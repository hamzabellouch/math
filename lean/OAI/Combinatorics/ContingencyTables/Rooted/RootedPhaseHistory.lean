import OAI.Combinatorics.ContingencyTables.Rooted.RootedRestartTrial
import OAI.Combinatorics.ContingencyTables.Rooted.RootedStoredHistory
import OAI.Combinatorics.ContingencyTables.Machines.FiniteWordPadding

namespace OAI

/-! # Actual adaptive phases on a common finite Boolean word space -/

namespace ContingencyTables.RootedPhaseHistory

open CommonBasesFPRAS FirstSuccess FairBits CompanionFactorialApplication
open CompanionRationalUpdates CompanionOracleDensity
open CompanionPhaseWords (Stored)
open CompanionTraceWords (eventIndicator)
open CompanionBooleanPhase (stepBits)
open RootedStoredHistory
open TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

structure Settings (A : Instance I J) where
  C : ℕ
  K : ℕ
  H : ℕ
  L : ℕ
  k : ℕ
  n : ℕ
  N : ℕ
  h : ℕ
  hK : 1 ≤ K
  hW : 100*A.d*K ≤ A.W
  xi : ℚ
  v : Grid (I := Fin (dimension A)) K

def width (A : Instance I J) (s : Settings A) (j : ℕ) : ℕ :=
  RootedRestartWords.initialStageBits A s.C s.K s.H s.L s.k s.n s.h j s.xi+
    (s.N*stepBits A s.C s.K j s.k s.xi+
      CompanionPhaseWords.phaseBits A s.C s.K j (s.N+1) s.xi)

def totalWidth (A : Instance I J) (s : Settings A) : ℕ :=
  ∑ j : Fin s.H,width A s j.val

abbrev Word (A : Instance I J) (s : Settings A) := Fin (totalWidth A s) → Bool

def split (A : Instance I J) (s : Settings A) (j : ℕ) :
    (Fin (width A s j) → Bool) ≃
      RootedRestartTrial.Words A s.C s.K s.H s.L j s.k s.n s.N s.h s.xi :=
  (splitWordEquiv _ _).trans (Equiv.prodCongr (Equiv.refl _)
    (splitWordEquiv _ _))

private lemma value_le_sum {N : ℕ} (f : Fin N → ℕ) (i : Fin N) :
    f i ≤ ∑ j,f j :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

lemma width_le (A : Instance I J) (s : Settings A) (j : ℕ) (hj : j < s.H) :
    width A s j ≤ totalWidth A s := by
  have h := value_le_sum (fun i : Fin s.H => width A s i.val) ⟨j,hj⟩
  exact h

def step (A : Instance I J) (R : RootedCompletion.Selection A.T) (s : Settings A)
    (history : List (Stored A)) (bits : Word A s) : Stored A :=
  let j := history.length
  let old := lookup A history j
  if hj : j < s.H then
    (RootedRestartTrial.run A R s.C s.K s.H s.L j s.k s.n s.N s.h s.hK s.hW s.xi s.v
      (fun i => (lookup A history i).multiplier) old.estimate
      (split A s j (prefixWord (width_le A s j hj) bits))).getD old
  else old

def decoded (A : Instance I J) (R : RootedCompletion.Selection A.T) (s : Settings A)
    (words : List (Word A s)) : List (Stored A) :=
  words.foldl (fun history bits => history++[step A R s history bits]) []

lemma decoded_nil (A : Instance I J) (R : RootedCompletion.Selection A.T) (s : Settings A) :
    decoded A R s []=[] := rfl

lemma decoded_snoc (A : Instance I J) (R : RootedCompletion.Selection A.T) (s : Settings A)
    (words : List (Word A s)) (bits : Word A s) :
    decoded A R s (words++[bits])=
      decoded A R s words++[step A R s (decoded A R s words) bits] := by
  simp only [decoded,List.foldl_append,List.foldl_cons,List.foldl_nil]

private lemma fold_length {X Y : Type*} (f : List Y → X → Y) (xs : List X) (ys : List Y) :
    (xs.foldl (fun history x => history++[f history x]) ys).length=ys.length+xs.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons,ih,List.length_append,List.length_cons,List.length_nil]
    omega

lemma decoded_length (A : Instance I J) (R : RootedCompletion.Selection A.T) (s : Settings A)
    (words : List (Word A s)) : (decoded A R s words).length=words.length := by
  simpa only [decoded,List.length_nil,Nat.zero_add] using fold_length (step A R s) words []

lemma good_snoc_iff (A : Instance I J) (R : RootedCompletion.Selection A.T) (s : Settings A)
    (eta : ℝ) (words : List (Word A s)) (bits : Word A s) :
    Good A R s.xi eta (decoded A R s (words++[bits])) ↔
      Good A R s.xi eta (decoded A R s words) ∧
        RootedPhaseTrial.ValidOutput A R words.length
          (lookup A (decoded A R s words) words.length) s.xi eta
          (step A R s (decoded A R s words) bits) := by
  rw [decoded_snoc,RootedStoredHistory.good_snoc,decoded_length]

end
end ContingencyTables.RootedPhaseHistory

end OAI
