import OAI.Geometry.SurfaceImmersion.Correction.PolynomialInverseChartJets
import OAI.Geometry.SurfaceImmersion.Atlas.WeightedInverseJacobian

namespace OAI

/-! Polynomial inverse-chart jets from forward jets and the actual Jacobian
lower bound. The exponent is fixed before the chart and numerical bounds. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes WeightedEstimates

lemma inverse_chart_derivative_eq_field
    (e : OpenPartialHomeomorph Base Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm) {y : Base} (hy : y ∈ e.target) :
    fderiv ℝ e.symm y = inverseJacobianField (fderiv ℝ e) (e.symm y) := by
  have hdet := coordDet_fderiv_ne_zero_of_local_inverse e.open_source e.open_target
    he.contDiffOn hi.contDiffOn (fun x hx => e.map_source hx)
    (fun x hx => e.left_inv hx) (e.map_target hy)
  have hleft := inverse_matrix_comp (fderiv ℝ e (e.symm y)) hdet
  have hright := inverse_chart_derivative e he hi hy
  change fderiv ℝ e.symm y =
    (coordDet (fderiv ℝ e (e.symm y)))⁻¹ • planeAdjugate (fderiv ℝ e (e.symm y))
  rw [← ContinuousLinearMap.id_comp (fderiv ℝ e.symm y),← hleft,
    ContinuousLinearMap.comp_assoc,hright,ContinuousLinearMap.comp_id]

theorem polynomial_inverse_chart_bound (m : ℕ) :
    ∃ d : ℕ, ∃ C : ℝ, 1 ≤ C ∧
    ∀ (e : OpenPartialHomeomorph Base Base),
      ContDiff ℝ ∞ e → ContDiff ℝ ∞ e.symm →
    ∀ B : ℝ, 1 ≤ B →
      (∀ j, 1 ≤ j → j ≤ m+1 → ∀ x ∈ e.source,
        ‖iteratedFDerivWithin ℝ j e e.source x‖ ≤ B) →
      (∀ x ∈ e.source, ‖(coordDet (fderiv ℝ e x))⁻¹‖ ≤ B) →
      ∀ j, 1 ≤ j → j ≤ m+1 → ∀ y ∈ e.target,
        ‖iteratedFDerivWithin ℝ j e.symm e.target y‖ ≤ C*B^d := by
  have hpoly := (inverseChartJetBudget_polynomial (m+1)).comp
    ((polynomialBound_const zero_le_one).add
      (inverseJacobianBudget_polynomial m (fun x => x) (fun x => x)
        polynomialBound_id polynomialBound_id))
    (fun B hB => le_add_of_nonneg_right (by
      dsimp [inverseJacobianBudget]
      have hB0 := zero_le_one.trans hB
      positivity))
  obtain ⟨d,C,hC,hpoly⟩ := hpoly
  refine ⟨d,C,hC,?_⟩
  intro e he hi B hB hfwd hdet j hj hjm y hy
  have hB0 := zero_le_one.trans hB
  have hA : ContDiffOn ℝ ∞ (fderiv ℝ e) e.source :=
    (he.fderiv_right (m := ∞) (by simp)).contDiffOn
  have hbA : WeightedBound e.source 1 m B (fderiv ℝ e) := by
    intro k hk x hx
    simp only [one_pow,one_mul]
    have hsame := iteratedFDerivWithin_congr
      (fun z hz => fderivWithin_of_isOpen e.open_source hz
        (𝕜 := ℝ) (f := (e : Base → Base))) hx (𝕜 := ℝ) (n := k)
    rw [← hsame,norm_iteratedFDerivWithin_fderivWithin e.open_source.uniqueDiffOn hx]
    exact hfwd (k+1) (by omega) (by omega) x hx
  have hne : ∀ x ∈ e.source, coordDet (fderiv ℝ e x) ≠ 0 := fun x hx =>
    coordDet_fderiv_ne_zero_of_local_inverse e.open_source e.open_target
      he.contDiffOn hi.contDiffOn (fun z hz => e.map_source hz) (fun z hz => e.left_inv hz) hx
  have hbJ := weighted_inverseJacobianField e.open_source.uniqueDiffOn hA
    zero_lt_one hB hB hbA hne hdet
  have hJ := contDiffOn_inverseJacobianField hA hne
  have hbound : ∀ k ≤ m, ∀ x ∈ e.source,
      ‖iteratedFDerivWithin ℝ k (inverseJacobianField (fderiv ℝ e)) e.source x‖ ≤
        1+inverseJacobianBudget m B B := by
    intro k hk x hx
    have hh := hbJ k hk x hx
    simp only [one_pow,one_mul] at hh
    exact hh.trans (le_add_of_nonneg_left zero_le_one)
  have hJB : 0 ≤ 1+inverseJacobianBudget m B B := by
    dsimp [inverseJacobianBudget]
    positivity
  exact (inverse_chart_positive_jets e hi (inverseJacobianField (fderiv ℝ e)) hJ
    (fun z hz => inverse_chart_derivative_eq_field e he hi hz) hJB hbound j hj hjm y hy).trans
      (hpoly B hB).2

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
