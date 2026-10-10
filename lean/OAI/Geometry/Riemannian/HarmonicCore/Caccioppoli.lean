import OAI.Geometry.Riemannian.HarmonicCore.Multipliers
import OAI.Geometry.Riemannian.HarmonicCore.Energy

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix InnerProductSpace Matrix.Norms.Elementwise
open scoped NNReal ENNReal

namespace HarmonicCounterexample.Main.SmoothMetric3
theorem weak_caccioppoli (R S : ℝ) (A : E3 → E3 →L[ℝ] E3) (C c : ℝ) (hc : 0 < c)
    (hA : AEStronglyMeasurable A (volume : Measure E3))
    (hbound : ∀ x, ‖A x‖ ≤ C) (hpos : ∀ x v, c * ‖v‖^2 ≤ ⟪A x v,v⟫_ℝ)
    (u : ZeroSobolev S)
    (hu : ∀ v : ZeroSobolev R,
      ⟪coefficientCLM A C hA hbound (sobolevDerivative S u),sobolevDerivative R v⟫_ℝ = 0)
    (χ : E3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hsupp : tsupport χ ⊆ Metric.ball 0 R)
    (K D : ℝ) (hK : ∀ x, ‖χ x‖ ≤ K) (hD : ∀ x, ‖gradient χ x‖ ≤ D) :
    ‖scalarFieldCLM χ hχ.continuous K hK (sobolevDerivative S u)‖ ≤
      (2*C/c) * ‖gradientFieldCLM χ hχ D hD (sobolevValue S u)‖ := by
  let T : DerivativeL2 →L[ℝ] DerivativeL2 := scalarFieldCLM χ hχ.continuous K hK
  let B : DerivativeL2 →L[ℝ] DerivativeL2 := coefficientCLM A C hA hbound
  let du : DerivativeL2 := sobolevDerivative S u
  let p : DerivativeL2 := T du
  let q : DerivativeL2 := gradientFieldCLM χ hχ D hD (sobolevValue S u)
  let v := cutoffSobolev R S χ hχ hsupp K D hK hD u
  let w := localizeSobolev R χ hχ K D hK hD v
  have hw : sobolevDerivative R w = T (p+q) + T q := by
    change T (p+q) + gradientFieldCLM χ hχ D hD
      (scalarFieldCLM χ hχ.continuous K hK (sobolevValue S u)) = _
    rw [gradientField_scalar_commute]
  have hmove (z : DerivativeL2) : ⟪B du,T z⟫_ℝ = ⟪B p,z⟫_ℝ := by
    change ⟪coefficientCLM A C hA hbound du,scalarFieldCLM χ hχ.continuous K hK z⟫_ℝ = _
    rw [← scalarField_inner,scalarField_coefficient_commute]
  have he : ⟪B p,p⟫_ℝ + 2 * ⟪B p,q⟫_ℝ = 0 := by
    have h := hu w
    change ⟪B du,sobolevDerivative R w⟫_ℝ = 0 at h
    rw [hw,inner_add_right,hmove,hmove,inner_add_right] at h
    linarith
  have hp : c * ‖p‖^2 ≤ ⟪B p,p⟫_ℝ := coefficientCLM_coercive A C c hA hbound hpos p
  have hcross := real_inner_le_norm (-(B p)) q
  rw [inner_neg_left,norm_neg] at hcross
  have hnorm : ‖B p‖ ≤ C * ‖p‖ := coefficientLinear_norm A C hA hbound p
  have hle : c * ‖p‖^2 ≤ (2*C) * ‖p‖ * ‖q‖ := by
    have := mul_le_mul_of_nonneg_right hnorm (norm_nonneg q)
    nlinarith
  have hC : 0 ≤ C := (norm_nonneg (A 0)).trans (hbound 0)
  change ‖p‖ ≤ (2*C/c) * ‖q‖
  by_cases hz : ‖p‖ = 0
  · rw [hz]; positivity
  · have hp0 : 0 < ‖p‖ := (norm_nonneg p).lt_of_ne' hz
    have hle' : c * ‖p‖ ≤ (2*C) * ‖q‖ := by
      apply (mul_le_mul_iff_left₀ hp0).mp
      nlinarith [hle]
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hc).mpr (by simpa [mul_comm] using hle')

end HarmonicCounterexample.Main.SmoothMetric3

end

end OAI
