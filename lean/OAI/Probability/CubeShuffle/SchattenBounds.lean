import OAI.Probability.CubeShuffle.WeightedModel

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace CubeShuffle.WeightedSweep
open Specht UnitaryFinite

lemma dimension_pos (μ : YoungDiagram) : 0 < dimension μ := by
  unfold dimension
  exact_mod_cast Specht.dimension_pos μ

lemma dimension_one_le (μ : YoungDiagram) : 1 ≤ dimension μ := by
  unfold dimension
  exact_mod_cast (show 1 ≤ Module.finrank ℂ (space μ) from Specht.dimension_pos μ)

lemma log_dimension_nonneg (μ : YoungDiagram) : 0 ≤ Real.log (dimension μ) :=
  Real.log_nonneg (dimension_one_le μ)

section Schatten
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V]

lemma schattenMoment_nonneg (A : V →L[ℂ] V) (p : ℝ) : 0 ≤ schattenMoment A p :=
  Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (A.toLinearMap.singularValues_nonneg i) _)

lemma schattenNorm_rpow (A : V →L[ℂ] V) {p : ℝ} (hp : p ≠ 0) :
    schattenNorm A p ^ p = schattenMoment A p := by
  rw [schattenNorm, ← Real.rpow_mul (schattenMoment_nonneg A p)]
  rw [one_div_mul_cancel hp, Real.rpow_one]

lemma singularValue_le_norm (A : V →L[ℂ] V) (i : Fin (Module.finrank ℂ V)) :
    A.toLinearMap.singularValues i ≤ ‖A‖ := by
  let T := A.toLinearMap
  let hT := T.isSymmetric_adjoint_comp_self
  let b := hT.eigenvectorBasis rfl
  have hnonneg := T.isPositive_adjoint_comp_self.nonneg_eigenvalues rfl i
  have heig := hT.apply_eigenvectorBasis rfl i
  have hn := (A.adjoint.comp A).le_opNorm (b i)
  change ‖(T.adjoint.comp T) (b i)‖ ≤ ‖A.adjoint.comp A‖ * ‖b i‖ at hn
  rw [heig, norm_smul, RCLike.norm_ofReal,
    abs_of_nonneg hnonneg, b.norm_eq_one, mul_one, mul_one,
    ContinuousLinearMap.norm_adjoint_comp_self] at hn
  apply le_of_sq_le_sq ?_ (norm_nonneg A)
  rw [T.sq_singularValues_fin rfl i]
  simpa [sq] using hn

lemma schattenMoment_le (A : V →L[ℂ] V) {p : ℝ} (hp : 0 ≤ p) :
    schattenMoment A p ≤ (Module.finrank ℂ V : ℝ) * ‖A‖ ^ p := by
  calc
    _ ≤ ∑ _i : Fin (Module.finrank ℂ V), ‖A‖ ^ p :=
      Finset.sum_le_sum (fun i _ => Real.rpow_le_rpow
        (A.toLinearMap.singularValues_nonneg i) (singularValue_le_norm A i) hp)
    _ = _ := by simp

end Schatten

end CubeShuffle.WeightedSweep

end

end OAI
