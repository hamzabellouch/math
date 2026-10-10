import OAI.Combinatorics.ContingencyTables.Sampling.UnitFiniteLaw
import OAI.Combinatorics.ContingencyTables.Transport.ListedIntegerLaw

namespace OAI

/-! # Integer counts for the all-small sampler's actual random words -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open FirstSuccess FairBits CompletionCounts ResidualMixture SmallContextCoordinates
open scoped BigOperators Classical
noncomputable section

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)

def unitStepCounts (x : PaperStates r c) : IntegerLaw (PaperStates r c) (2^s) :=
  (IntegerLaw.boolean s).push (unitCodeBitStep r c e x)

lemma unitStepCounts_law (htotal : ∑ i,r i=∑ j,c j) (x : PaperStates r c) :
    (unitStepCounts r c e x).toRational (by positivity)=unitSmallStep r c x := by
  unfold unitStepCounts
  rw [IntegerLaw.toRational_push,IntegerLaw.toRational_boolean,unitCodeBitStep_law r c e htotal]

attribute [local irreducible] unitStepCounts unitSmallStep

def unitWalkCounts (x : PaperStates r c) (N : ℕ) :
    IntegerLaw (PaperStates r c) ((2^s)^N) := IntegerLaw.walk (unitStepCounts r c e) x N

attribute [local irreducible] unitWalkCounts

lemma unitWalkCounts_law (htotal : ∑ i,r i=∑ j,c j) (x : PaperStates r c) (N : ℕ) :
    (unitWalkCounts r c e x N).toRational (by positivity)=walkLaw (unitSmallStep r c) x N := by
  unfold unitWalkCounts
  rw [IntegerLaw.toRational_walk _ (by positivity)]
  have he : (fun y => (unitStepCounts r c e y).toRational (by positivity))=unitSmallStep r c := by
    funext y
    exact unitStepCounts_law r c e htotal y
  exact congrArg (fun K => walkLaw K x N) he

def unitTrialCounts (hsmall : ∀ i j,paperSmall r c i j=true) (x : PaperStates r c) (N : ℕ) :
    IntegerLaw (Option (Table r c)) ((2^s)^N) :=
  (unitWalkCounts r c e x N).push (fun y => stateTrial r c ⟨y,allSmallFibre r c hsmall y⟩)

def unitOuterCounts (hsmall : ∀ i j,paperSmall r c i j=true)
    (x : PaperStates r c) (N J : ℕ) (fallback : Table r c) :
    IntegerLaw (Table r c) (((2^s)^N)^J) :=
  (unitTrialCounts r c e hsmall x N).retry fallback J

lemma unitTrialCounts_law (htotal : ∑ i,r i=∑ j,c j)
    (hsmall : ∀ i j,paperSmall r c i j=true) (x : PaperStates r c) (N : ℕ) :
    (unitTrialCounts r c e hsmall x N).toRational (by positivity)=
      mapLaw (uniformLaw (α := Fin (N*s) → Bool))
        (fun bits => stateTrial r c (unitCodeJointDraw r c e (allSmallFibre r c hsmall) x N bits)) := by
  unfold unitTrialCounts unitCodeJointDraw
  rw [IntegerLaw.toRational_push,unitWalkCounts_law r c e htotal,←flatUnitCodeWalk_law r c e htotal,
    mapLaw_comp]

lemma unitOuterCounts_law (htotal : ∑ i,r i=∑ j,c j)
    (hsmall : ∀ i j,paperSmall r c i j=true) (x : PaperStates r c) (N J : ℕ) (fallback : Table r c) :
    (unitOuterCounts r c e hsmall x N J fallback).toRational (by positivity)=
      mapLaw (uniformLaw (α := Fin (J*(N*s)) → Bool))
        (unitCodeOuterDraw r c e (allSmallFibre r c hsmall) x N J fallback) := by
  unfold unitOuterCounts unitCodeOuterDraw
  rw [IntegerLaw.toRational_retry _ (by positivity),unitTrialCounts_law r c e htotal]
  rw [←map_equiv (GridBoundary.gridWordEquiv J (N*s)),uniform_equiv]
  rw [retryLaw_map]
  exact (wordRetryLaw_eq
    (fun bits : Fin (N*s) → Bool => stateTrial r c
      (unitCodeJointDraw r c e (allSmallFibre r c hsmall) x N bits)) fallback J).symm

end
end ContingencyTables.SmallGraphProfiles

end OAI
