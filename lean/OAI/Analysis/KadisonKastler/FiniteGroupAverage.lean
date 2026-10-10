import OAI.Analysis.KadisonKastler.BoundaryBoundedTransport

namespace OAI

/-! # The normalized finite-group mean

Finite averaging gives the equivariant bimodule mean needed by quadratic correction, for every C-star algebra of values.
-/

namespace KadisonKastler

open scoped BigOperators BoundedContinuousFunction

noncomputable section

variable {G B : Type*} [Group G] [Fintype G] [TopologicalSpace G]
  [DiscreteTopology G] [CStarAlgebra B]

/-- Normalized counting average on bounded functions. -/
def finiteGroupAverage : (G →ᵇ B) →L[ℂ] B :=
  ((Fintype.card G : ℝ)⁻¹) • ∑ g : G, BoundedContinuousFunction.evalCLM ℂ g

omit [Group G] [DiscreteTopology G] in
@[simp]
theorem finiteGroupAverage_apply (f : G →ᵇ B) :
    finiteGroupAverage f = ((Fintype.card G : ℝ)⁻¹) • ∑ g : G, f g := by
  simp [finiteGroupAverage]

omit [DiscreteTopology G] in
theorem finiteGroupAverage_norm_le (f : G →ᵇ B) :
    ‖finiteGroupAverage f‖ ≤ ‖f‖ := by
  have hc : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  rw [finiteGroupAverage_apply, norm_smul, Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (Fintype.card G : ℝ)⁻¹ * ∑ g : G, ‖f g‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (Fintype.card G : ℝ)⁻¹ * ∑ _g : G, ‖f‖ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun g _ => f.norm_coe_le_norm g)
    _ = ‖f‖ := by simp [Finset.sum_const, nsmul_eq_mul, hc.ne']

omit [DiscreteTopology G] in
@[simp]
theorem finiteGroupAverage_const (b : B) :
    finiteGroupAverage (BoundedContinuousFunction.const G b) = b := by
  have hc : (Fintype.card G : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card G ≠ 0)
  rw [finiteGroupAverage_apply]
  simp only [BoundedContinuousFunction.const_apply, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hc, one_smul]

omit [Group G] [DiscreteTopology G] in
theorem finiteGroupAverage_star (f : G →ᵇ B) :
    finiteGroupAverage (star f) = star (finiteGroupAverage f) := by
  simp only [finiteGroupAverage_apply, star_smul, star_trivial, star_sum,
    BoundedContinuousFunction.star_apply]

omit [Group G] [DiscreteTopology G] in
theorem finiteGroupAverage_left (b : B) (f : G →ᵇ B) :
    finiteGroupAverage (boundaryConstant b * f) = b * finiteGroupAverage f := by
  simp only [finiteGroupAverage_apply, BoundedContinuousFunction.mul_apply,
    boundaryConstant_apply, Finset.mul_sum, mul_smul_comm]

omit [Group G] [DiscreteTopology G] in
theorem finiteGroupAverage_right (f : G →ᵇ B) (b : B) :
    finiteGroupAverage (f * boundaryConstant b) = finiteGroupAverage f * b := by
  simp only [finiteGroupAverage_apply, BoundedContinuousFunction.mul_apply,
    boundaryConstant_apply, Finset.sum_mul, smul_mul_assoc]

/-- Normalized counting measure is invariant under left translation. -/
theorem finiteGroupAverage_translate (g : G) (f : G →ᵇ B) :
    finiteGroupAverage (boundaryTranslate (1 : G →* (B ≃⋆ₐ[ℂ] B)) g f) =
      finiteGroupAverage f := by
  simp only [finiteGroupAverage_apply, boundaryTranslate_apply,
    MonoidHom.one_apply, StarAlgEquiv.one_apply]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft g⁻¹) _ _ (fun _ => rfl)

/-- The finite-group mean, with both module identities. -/
def finiteGroupBimoduleMean : BimoduleMean (boundaryConstant (G := G) (B := B)) where
  toCLM := finiteGroupAverage
  map_one := finiteGroupAverage_const (G := G) (1 : B)
  map_star := finiteGroupAverage_star
  norm_le := finiteGroupAverage_norm_le
  map_left := finiteGroupAverage_left
  map_right := finiteGroupAverage_right

end

end KadisonKastler

end OAI
