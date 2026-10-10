import OAI.Combinatorics.ContingencyTables.Transport.CanonicalIntegerLaw
import OAI.Combinatorics.ContingencyTables.Transport.BooleanIntegerLaw
import OAI.Combinatorics.ContingencyTables.Transport.ListedBooleanDraw

namespace OAI

/-! # Integer transition counts for the actual outer-profile walk -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open CompletionCounts SmallContextCoordinates ResidualMixture FirstSuccess FairBits CompletionTranslation
open scoped BigOperators Classical
noncomputable section

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
variable (hr : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
variable (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2)≤b)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "R" => listedRows r c (d^20) (d^12) (stateCapacity r c) hr
local notation "P" => listedColumns r c (d^20) (d^12) (stateCapacity r c) hc
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)
local notation "f" => 25*(d+b+h+1)^62

def listedCompletionCounts (x : PaperStates r c) : IntegerLaw (PaperFibre r c x) (2^f) :=
  (paddedCanonicalCounts (R x) (P x) (listed_dimension_fourteen r c hr hc)
    (listed_row_padding r c (d^20) (d^12) (stateCapacity r c) hr hc x)
    (listed_column_padding r c (d^20) (d^12) (stateCapacity r c) hr hc x)
    (listed_paper_totals r c hr hc x) h f (listedDrawBits_le r c hr hc b h hb x)).equiv
      (paperListedEquiv r c hr hc x).symm

lemma listedCompletionCounts_law (x : PaperStates r c) :
    (listedCompletionCounts r c hr hc b h hb x).toRational (by positivity)=
      mapLaw (uniformLaw (α := Fin f → Bool)) (listedPaddedDraw r c hr hc b h hb x) := by
  unfold listedCompletionCounts
  rw [IntegerLaw.toRational_equiv,paddedCanonicalCounts_law]
  unfold listedPaddedDraw listedDenseDraw
  rw [mapLaw_equiv_output]

/-- Completion counts are cached once per state; only the short proposal
word is enumerated to form this finite transition matrix. -/
def listedStepCounts (x : PaperStates r c) : IntegerLaw (PaperStates r c) (2^(s+f)) :=
  IntegerLaw.booleanFinish (listedCompletionCounts r c hr hc b h hb x)
    (fun word A => completionDecision R P x (decodedCodeProposal r c e x word)
      (paperListedEquiv r c hr hc x A))

lemma listedStepCounts_law (htotal : ∑ i,r i=∑ j,c j) (x : PaperStates r c) :
    (listedStepCounts r c e hr hc b h hb x).toRational (by positivity)=
      listedSmallKernel r c hr hc b h hb x := by
  unfold listedStepCounts
  rw [IntegerLaw.toRational_booleanFinish _ _ _
    (listedCompletionCounts_law r c hr hc b h hb x)]
  have he : (fun bits : Fin (s+f) → Bool =>
      completionDecision R P x (decodedCodeProposal r c e x (splitWordEquiv s f bits).1)
        (paperListedEquiv r c hr hc x
          (listedPaddedDraw r c hr hc b h hb x (splitWordEquiv s f bits).2)))=
      listedBitStep r c e hr hc b h hb x := by
    funext bits
    rw [listed_completionDecision r c hr hc]
    rfl
  rw [he]
  exact listedBitStep_law r c e hr hc b h hb htotal x

attribute [local irreducible] listedStepCounts listedSmallKernel

/-- The complete adaptive walk is an integer matrix power. -/
def listedWalkCounts (x : PaperStates r c) (N : ℕ) :
    IntegerLaw (PaperStates r c) ((2^(s+f))^N) :=
  IntegerLaw.walk (listedStepCounts r c e hr hc b h hb) x N

attribute [local irreducible] listedWalkCounts

lemma listedWalkCounts_law (htotal : ∑ i,r i=∑ j,c j) (x : PaperStates r c) (N : ℕ) :
    (listedWalkCounts r c e hr hc b h hb x N).toRational (by positivity)=
      walkLaw (listedSmallKernel r c hr hc b h hb) x N := by
  unfold listedWalkCounts
  rw [IntegerLaw.toRational_walk]
  congr 1
  funext y
  exact listedStepCounts_law r c e hr hc b h hb htotal y

/-- Each final table count sums over the reached profile and its fresh
terminal completion; failed outer trials retain their exact numerator. -/
def listedTrialCounts (x : PaperStates r c) (N : ℕ) :
    IntegerLaw (Option (Table r c)) ((2^(s+f))^N*2^f) :=
  (listedWalkCounts r c e hr hc b h hb x N).bind
    (fun y => (listedCompletionCounts r c hr hc b h hb y).push
      (fun A => stateTrial r c ⟨y,A⟩))

lemma listedTrialCounts_law (htotal : ∑ i,r i=∑ j,c j) (x : PaperStates r c) (N : ℕ) :
    (listedTrialCounts r c e hr hc b h hb x N).toRational (by positivity)=
      mapLaw (listedJointLaw r c hr hc b h hb x N) (stateTrial r c) := by
  unfold listedTrialCounts
  rw [IntegerLaw.toRational_bind _ _ (by positivity) (by positivity),
    listedWalkCounts_law r c e hr hc b h hb htotal]
  have hf (y : PaperStates r c) :
      ((listedCompletionCounts r c hr hc b h hb y).push
        (fun A => stateTrial r c ⟨y,A⟩)).toRational (by positivity)=
      mapLaw (listedFibreLaw r c hr hc b h hb y) (fun A => stateTrial r c ⟨y,A⟩) := by
    rw [IntegerLaw.toRational_push]
    exact congrArg (fun p => mapLaw p (fun A => stateTrial r c ⟨y,A⟩))
      (listedCompletionCounts_law r c hr hc b h hb y)
  have hk := funext hf
  rw [hk]
  apply RationalLaw.ext
  funext T
  simp only [mapLaw,listedJointLaw,listedFibreLaw,dependentJointLaw,bindLaw,
    Fintype.sum_sigma,Finset.mul_sum,mul_ite,mul_zero]

def listedOuterCounts (x : PaperStates r c) (N J : ℕ) (fallback : Table r c) :
    IntegerLaw (Table r c) (((2^(s+f))^N*2^f)^J) :=
  (listedTrialCounts r c e hr hc b h hb x N).retry fallback J

lemma listedOuterCounts_law (htotal : ∑ i,r i=∑ j,c j) (x : PaperStates r c)
    (N J : ℕ) (fallback : Table r c) :
    (listedOuterCounts r c e hr hc b h hb x N J fallback).toRational (by positivity)=
      mapLaw (uniformLaw (α := Fin (J*(N*(s+f)+f)) → Bool))
        (listedOuterDraw r c e hr hc b h hb x N J fallback) := by
  unfold listedOuterCounts
  rw [IntegerLaw.toRational_retry _ (by positivity),
    listedTrialCounts_law r c e hr hc b h hb htotal,
    retryLaw_map,listedOuterDraw_law r c e hr hc b h hb htotal]
  rfl

end
end ContingencyTables.SmallGraphProfiles

end OAI
