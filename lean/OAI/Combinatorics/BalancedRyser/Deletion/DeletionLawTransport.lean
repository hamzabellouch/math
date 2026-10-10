import OAI.Combinatorics.BalancedRyser.Deletion.DeletionDomination2
import OAI.Combinatorics.BalancedRyser.Deletion.DeletionLawPMF

namespace OAI

open scoped BigOperators

namespace Balanced
open scoped _root_.Balanced

universe u

variable (F : Type u) [Field F] [Fintype F] [DecidableEq F]

theorem returnedDeletionLaw_dominated
    {κ : DeletionLaw.Weight (Fintype.card F) (Fintype.card F + 1)}
    {K a₀ : ℝ} (hq : 3 ≤ Fintype.card F) (hK : 0 ≤ K) (ha₀ : 0 < a₀)
    (hκ : DeletionLaw.IsSubprobabilityKernel κ)
    (hdistinct : DeletionLaw.DistinctOutput κ)
    (hcyl : DeletionLaw.CylinderBound κ K)
    (hsuccess : a₀ ≤ DeletionLaw.successMass κ) :
    DeletionDominated 3 (a₀⁻¹ + 4 * K)
      (returnedDeletionLaw F hκ hdistinct (ha₀.trans_le hsuccess)) := by
  intro D
  rw [returnedDeletionLaw_apply_toReal]
  let d := (validArrayDeletionEquiv F).symm D
  have hfinite := DeletionLaw.finite_domination
    (Fintype.card F) (Fintype.card F + 1) hq κ K a₀ hK ha₀
    hκ hdistinct hcyl hsuccess d.val d.property
  have henvelope := BalancedRyser.deletion_ratio_exponential_envelope
    ha₀ hK (show 1 ≤ Fintype.card F by omega)
  calc
    DeletionLaw.conditionedDeletionMass κ d.val ≤
        a₀⁻¹ * K ^ (2 * (Fintype.card F + 1)) *
          DeletionLaw.uniformDeletionMass (Fintype.card F) (Fintype.card F + 1) := hfinite
    _ ≤ Real.exp ((a₀⁻¹ + 4 * K) * (Fintype.card F : ℝ)) *
          DeletionLaw.uniformDeletionMass (Fintype.card F) (Fintype.card F + 1) :=
      mul_le_mul_of_nonneg_right henvelope
        (by unfold DeletionLaw.uniformDeletionMass; positivity)
    _ = Real.exp ((a₀⁻¹ + 4 * K) * (Fintype.card F : ℝ)) *
          uniformDeletionMass (F := F) 3 := by
      rw [geometric_uniformDeletionMass_eq]
      rfl

theorem exists_uniform_returnedDeletionLaw_domination_constant
    (K a₀ : ℝ) (hK : 0 ≤ K) (ha₀ : 0 < a₀) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
        3 ≤ Fintype.card F →
        ∀ (κ : DeletionLaw.Weight (Fintype.card F) (Fintype.card F + 1))
          (hκ : DeletionLaw.IsSubprobabilityKernel κ)
          (hdistinct : DeletionLaw.DistinctOutput κ),
          DeletionLaw.CylinderBound κ K →
          ∀ hsuccess : a₀ ≤ DeletionLaw.successMass κ,
            DeletionDominated 3 C
              (returnedDeletionLaw F hκ hdistinct (ha₀.trans_le hsuccess)) := by
  refine ⟨a₀⁻¹ + 4 * K,
    BalancedRyser.deletion_ratio_exponential_coefficient_pos ha₀ hK, ?_⟩
  intro F _ _ _ hq κ hκ hdistinct hcyl hsuccess
  exact returnedDeletionLaw_dominated F hq hK ha₀ hκ hdistinct hcyl hsuccess

theorem returnedDeletionLaw_event
    {κ : DeletionLaw.Weight (Fintype.card F) (Fintype.card F + 1)}
    (hκ : DeletionLaw.IsSubprobabilityKernel κ)
    (hdistinct : DeletionLaw.DistinctOutput κ)
    (hsuccess : 0 < DeletionLaw.successMass κ)
    (E : DeletionSet F 3 → Prop) [DecidablePred E] :
    deletionEventProbability (returnedDeletionLaw F hκ hdistinct hsuccess) E =
      ∑ D : DeletionLaw.ValidArray (Fintype.card F) (Fintype.card F + 1),
        if E (validArrayDeletionEquiv F D) then
          DeletionLaw.conditionedDeletionMass κ D.val else 0 := by
  classical
  unfold deletionEventProbability
  apply Fintype.sum_equiv (validArrayDeletionEquiv F).symm
  intro D
  simp [returnedDeletionLaw_apply_toReal]

end Balanced

end OAI
