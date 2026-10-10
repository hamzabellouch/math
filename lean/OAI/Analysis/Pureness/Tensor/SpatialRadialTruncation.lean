import OAI.Analysis.Pureness.Tensor.SpatialFreeGroupShell
import OAI.Analysis.Pureness.Tensor.SpatialFreeGroupRadial
import OAI.Analysis.Pureness.GroupAlgebra.GeometricShellSummability
import OAI.Analysis.Pureness.Operators.OperatorSeriesEigenvector
import OAI.Analysis.Pureness.Operators.OperatorApproximationEstimates

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped TensorProduct
open Filter Topology
local instance spatialRadialTruncationDecidableEq {X : Type*} : DecidableEq X := Classical.decEq X
variable {A H X : Type*} [CStarAlgebra A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hα : Function.Injective α)

def spatialRadialTruncation (r : ℝ) (m : ℕ) :
    representedSpatialTensor α (reducedGroupAlgebra (FreeGroup X)).subtype →L[ℂ]
      representedSpatialTensor α (reducedGroupAlgebra (FreeGroup X)).subtype :=
  ∑ k ∈ Finset.range m, ((r ^ k : ℝ) : ℂ) • spatialFreeGroupShell (X := X) α k

include hα in
lemma spatialRadialShell_summable (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun k : ℕ => ((r ^ k : ℝ) : ℂ) • spatialFreeGroupShell (X := X) α k) := by
  apply (geometric_shell_bound_summable r hr0 hr1).of_norm_bounded
  intro k
  have hnorm : ‖((r ^ k : ℝ) : ℂ)‖ = r ^ k := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hr0 k)]
  calc
    _ ≤ ‖((r ^ k : ℝ) : ℂ)‖ * ‖spatialFreeGroupShell (X := X) α k‖ :=
      ContinuousLinearMap.opNorm_smul_le _ _
    _ = r ^ k * ‖spatialFreeGroupShell (X := X) α k‖ :=
      congrArg (fun t : ℝ => t * ‖spatialFreeGroupShell (X := X) α k‖) hnorm
    _ ≤ _ := mul_le_mul_of_nonneg_left (spatialFreeGroupShell_opNorm_le (X := X) α hα k) (pow_nonneg hr0 k)

include hα in
theorem spatialFreeGroupRadial_eq_tsum_shells (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    spatialFreeGroupRadial (X := X) α r =
      ∑' k : ℕ, ((r ^ k : ℝ) : ℂ) • spatialFreeGroupShell (X := X) α k := by
  have hs := spatialRadialShell_summable (X := X) α hα r hr0 hr1
  have hr : |r| ≤ 1 := by rw [abs_of_nonneg hr0]; exact hr1.le
  have hg (a : A) (g : FreeGroup X) :
      spatialFreeGroupRadial (X := X) α r
        (spatialCompletionMap α (reducedGroupAlgebra (FreeGroup X)).subtype
          (a ⊗ₜ[ℂ] (reducedGroupUnitary (FreeGroup X) g : reducedGroupAlgebra (FreeGroup X)))) =
      (∑' k : ℕ, ((r ^ k : ℝ) : ℂ) • spatialFreeGroupShell (X := X) α k)
        (spatialCompletionMap α (reducedGroupAlgebra (FreeGroup X)).subtype
          (a ⊗ₜ[ℂ] (reducedGroupUnitary (FreeGroup X) g : reducedGroupAlgebra (FreeGroup X)))) := by
    refine (spatialFreeGroupRadial_generator α hα r hr a g).trans ?_
    apply (weighted_operator_series_apply (fun k => ((r ^ k : ℝ) : ℂ))
      (spatialFreeGroupShell (X := X) α) hs _ g.toWord.length ?_).symm
    intro k
    refine (spatialFreeGroupShell_generator α hα k a g).trans ?_
    by_cases hk : k = g.toWord.length
    · subst k
      simp only [freeGroupShellSymbol, ↓reduceIte, one_smul]
    · have hk' := Ne.symm hk
      simp only [freeGroupShellSymbol, ite_eq_right hk, ite_eq_right hk', zero_smul]
  apply ContinuousLinearMap.ext
  intro x
  refine (spatialGroupPolynomialMap_denseRange (G := FreeGroup X) α).induction_on x ?_ ?_
  · exact isClosed_eq (spatialFreeGroupRadial (X := X) α r).continuous (ContinuousLinearMap.continuous _)
  · intro a
    let R := spatialFreeGroupRadial (X := X) α r
    let S := ∑' k : ℕ, ((r ^ k : ℝ) : ℂ) • spatialFreeGroupShell (X := X) α k
    let v := fun g => spatialCompletionMap α (reducedGroupAlgebra (FreeGroup X)).subtype
      (a g ⊗ₜ[ℂ] (reducedGroupUnitary (FreeGroup X) g : reducedGroupAlgebra (FreeGroup X)))
    exact (congrArg R (spatialGroupPolynomialMap_apply (G := FreeGroup X) α a)).trans
      ((map_sum R v a.support).trans
        ((Finset.sum_congr rfl (fun g _ => hg (a g) g)).trans
          ((map_sum S v a.support).symm.trans
            (congrArg S (spatialGroupPolynomialMap_apply (G := FreeGroup X) α a)).symm)))

include hα in

theorem spatialRadialTruncation_tendsto (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Tendsto (fun m => spatialRadialTruncation (X := X) α r m) atTop
      (nhds (spatialFreeGroupRadial (X := X) α r)) := by
  have hc := (spatialRadialShell_summable (X := X) α hα r hr0 hr1).hasSum.tendsto_sum_nat
  exact (congrArg (fun z => Tendsto (fun m => spatialRadialTruncation (X := X) α r m)
    atTop (nhds z)) (spatialFreeGroupRadial_eq_tsum_shells (X := X) α hα r hr0 hr1)).mpr hc

include hα in

theorem exists_spatialRadialTruncation_bound (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    ∃ m : ℕ, n ≤ m ∧ ‖spatialRadialTruncation (X := X) α r m‖ ≤ 2 := by
  have hr : |r| ≤ 1 := by rw [abs_of_nonneg hr0]; exact hr1.le
  have hn : ‖spatialFreeGroupRadial (X := X) α r‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
      exact (spatialFreeGroupRadial_norm_le (X := X) α hα r hr x).trans_eq (one_mul _).symm)
  exact exists_norm_le_two_of_tendsto _ _
    (spatialRadialTruncation_tendsto (X := X) α hα r hr0 hr1) hn n
end CuntzPureness

end

end OAI
