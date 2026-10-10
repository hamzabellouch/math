import OAI.Analysis.KadisonKastler.GraphScaleResolvent
import OAI.Analysis.KadisonKastler.GraphResolventFunctionalCalculus

namespace OAI

/-! # Bounded functional calculus formula for every graph scale -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

def graphScaleScalar (c s : ℝ) : ℝ := s + c ^ 2 * (1 - s)

theorem graphScaleScalar_pos {c s : ℝ} (hc : c ≠ 0) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    0 < graphScaleScalar c s := by
  unfold graphScaleScalar
  by_cases hz : s = 0
  · simpa only [hz, sub_zero, mul_one, zero_add] using sq_pos_of_ne_zero hc
  · exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne hs (Ne.symm hz))
      (mul_nonneg (sq_nonneg c) (sub_nonneg.mpr hs1))

theorem graphScaleDenominator_eq_cfc (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ) :
    graphScaleDenominator M J Ω c = cfc (graphScaleScalar c) (graphResolvent M J Ω 1) := by
  have hR := (graphResolvent_positive (M := M) J Ω 1).isSelfAdjoint
  unfold graphScaleScalar
  rw [cfc_add _ (fun s : ℝ => s) (fun s : ℝ => c ^ 2 * (1 - s)) (by fun_prop) (by fun_prop),
    cfc_const_mul (c ^ 2) (fun s : ℝ => 1 - s) _ (by fun_prop),
    cfc_sub (fun _ : ℝ => 1) (fun s : ℝ => s) _ (by fun_prop) (by fun_prop),
    cfc_id' ℝ _ hR, cfc_const_one ℝ _ hR]
  change _ = _ + (c ^ 2) • _
  rw [← Complex.coe_smul, Complex.ofReal_pow]
  rfl

def graphScaleInverse (M : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H)
    (Ω : H) (c : ℝ) : H →L[ℂ] H :=
  cfc (fun s => (graphScaleScalar c s)⁻¹) (graphResolvent M J Ω 1)

theorem graphScaleInverse_continuousOn (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    {c : ℝ} (hc : c ≠ 0) :
    ContinuousOn (fun s => (graphScaleScalar c s)⁻¹) (spectrum ℝ (graphResolvent M J Ω 1)) := by
  apply ContinuousOn.inv₀ (by unfold graphScaleScalar; fun_prop)
  intro s hs
  have hb := graphResolvent_spectrum_bounds J Ω hs
  exact (graphScaleScalar_pos hc hb.1 hb.2).ne'

theorem graphScaleDenominator_mul_inverse (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    {c : ℝ} (hc : c ≠ 0) :
    graphScaleDenominator M J Ω c * graphScaleInverse M J Ω c = 1 := by
  rw [graphScaleDenominator_eq_cfc, graphScaleInverse,
    ← cfc_mul (graphScaleScalar c) (fun s => (graphScaleScalar c s)⁻¹) _
      (by unfold graphScaleScalar; fun_prop) (graphScaleInverse_continuousOn J Ω hc)]
  calc
    _ = cfc (fun _ : ℝ => 1) (graphResolvent M J Ω 1) := by
      apply cfc_congr
      intro s hs
      have hb := graphResolvent_spectrum_bounds J Ω hs
      exact mul_inv_cancel₀ (graphScaleScalar_pos hc hb.1 hb.2).ne'
    _ = 1 := cfc_const_one ℝ _ (graphResolvent_positive J Ω 1).isSelfAdjoint

theorem graphResolvent_eq_mul_scaleInverse (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    {c : ℝ} (hc : c ≠ 0) :
    graphResolvent M J Ω c = graphResolvent M J Ω 1 * graphScaleInverse M J Ω c := by
  calc
    _ = graphResolvent M J Ω c *
        (graphScaleDenominator M J Ω c * graphScaleInverse M J Ω c) := by
      rw [graphScaleDenominator_mul_inverse J Ω hc, mul_one]
    _ = _ := by rw [← mul_assoc, graphResolvent_mul_scaleDenominator]

/-- An arbitrary nonzero graph scale is a bounded rational function of the scale-one resolvent. -/
theorem graphResolvent_eq_cfc_scale (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    {c : ℝ} (hc : c ≠ 0) :
    graphResolvent M J Ω c =
      cfc (fun s => s / graphScaleScalar c s) (graphResolvent M J Ω 1) := by
  rw [graphResolvent_eq_mul_scaleInverse J Ω hc, graphScaleInverse]
  have hR := (graphResolvent_positive (M := M) J Ω 1).isSelfAdjoint
  conv_lhs => lhs; rw [← cfc_id' ℝ (graphResolvent M J Ω 1) hR]
  rw [← cfc_mul (fun s : ℝ => s) (fun s => (graphScaleScalar c s)⁻¹) _
    (by fun_prop) (graphScaleInverse_continuousOn J Ω hc)]
  simp only [div_eq_mul_inv]

end

end KadisonKastler

end OAI
