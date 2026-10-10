import OAI.MeasureTheory.Falconer.Slicing.GaussianRows

namespace OAI

/-! # Positive lower bounds for the Gaussian bands used in slice averaging -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

noncomputable def gaussianBandLowerConstant : ℝ :=
  2*(Real.sqrt (2*Real.pi))⁻¹*Real.exp (-(1/2:ℝ))

theorem gaussianBandLowerConstant_pos : 0 < gaussianBandLowerConstant := by
  unfold gaussianBandLowerConstant
  positivity

theorem standard_gaussian_band_lower {r : ℝ} (_hr : 0 ≤ r) (hr1 : r ≤ 1) :
    ENNReal.ofReal (gaussianBandLowerConstant*r) ≤ gaussianReal 0 1 (Icc (-r) r) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num),withDensity_apply _ measurableSet_Icc]
  calc
    _ = ∫⁻ _ in Icc (-r) r,
        ENNReal.ofReal ((Real.sqrt (2*Real.pi))⁻¹*Real.exp (-(1/2:ℝ))) := by
      rw [lintegral_const,Measure.restrict_apply_univ,Real.volume_Icc,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      unfold gaussianBandLowerConstant
      ring
    _ ≤ _ := by
      apply setLIntegral_mono' measurableSet_Icc
      intro x hx
      apply ENNReal.ofReal_le_ofReal
      simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero,one_div]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      have hab : |x| ≤ 1 := (abs_le.mpr hx).trans hr1
      have hsq : x^2 ≤ 1 := by nlinarith [sq_abs x,abs_nonneg x]
      linarith

theorem gaussian_unit_inner_band_lower {w : Space d} (hw : ‖w‖ = 1)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    ENNReal.ofReal (gaussianBandLowerConstant*r) ≤
      stdGaussian (Space d) {x | |inner ℝ w x| ≤ r} := by
  have he : {x : Space d | |inner ℝ w x| ≤ r} = (innerSL ℝ w) ⁻¹' Icc (-r) r := by
    ext x
    simp only [mem_ofPred_eq,mem_preimage,mem_Icc,innerSL_apply_apply,abs_le]
  rw [he,← Measure.map_apply (innerSL ℝ w).continuous.measurable measurableSet_Icc,
    gaussian_unit_inner_law hw]
  exact standard_gaussian_band_lower hr hr1

theorem gaussianRows_one_band_lower {w : Space d} (hw : ‖w‖ = 1)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    ENNReal.ofReal ((gaussianBandLowerConstant*r)^h) ≤
      gaussianRows d h {A | ∀ i, |inner ℝ w (A i)| ≤ r} := by
  have he : {A : Fin h → Space d | ∀ i, |inner ℝ w (A i)| ≤ r} =
      Set.pi univ (fun _ => {x : Space d | |inner ℝ w x| ≤ r}) := by ext A; simp
  rw [gaussianRows,he,Measure.pi_pi]
  calc
    _ = ∏ _ : Fin h, ENNReal.ofReal (gaussianBandLowerConstant*r) := by
      rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin,
        ← ENNReal.ofReal_pow (mul_nonneg gaussianBandLowerConstant_pos.le hr)]
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => gaussian_unit_inner_band_lower hw hr hr1)

end Falconer

end OAI
