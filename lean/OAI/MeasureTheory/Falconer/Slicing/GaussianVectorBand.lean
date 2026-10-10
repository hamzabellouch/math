import OAI.MeasureTheory.Falconer.Slicing.GaussianRows

namespace OAI

/-! # Gaussian bands for unnormalized point differences -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

noncomputable def gaussianVectorBandConstant : ℝ := 2*(1+gaussianBandConstant)

theorem gaussianVectorBandConstant_pos : 0 < gaussianVectorBandConstant := by
  unfold gaussianVectorBandConstant
  linarith [gaussianBandConstant_pos]

theorem gaussian_vector_band (z : Space d) {r : ℝ} (hr : 0 < r) :
    stdGaussian (Space d) {x | |inner ℝ z x| ≤ r} ≤
      ENNReal.ofReal (gaussianVectorBandConstant*r/(‖z‖+r)) := by
  have hc := gaussianBandConstant_pos
  have hd : 0 < ‖z‖+r := add_pos_of_nonneg_of_pos (norm_nonneg _) hr
  by_cases hz : ‖z‖ ≤ r
  · apply (prob_le_one : stdGaussian (Space d) {x | |inner ℝ z x| ≤ r} ≤ 1).trans
    apply ENNReal.one_le_ofReal.mpr
    apply (le_div_iff₀ hd).mpr
    unfold gaussianVectorBandConstant
    nlinarith
  · have hn : 0 < ‖z‖ := lt_trans hr (lt_of_not_ge hz)
    let u : Space d := ‖z‖⁻¹ • z
    have hu : ‖u‖ = 1 := by simp [u,norm_smul,hn.ne']
    have he : {x : Space d | |inner ℝ z x| ≤ r} =
        {x : Space d | |inner ℝ u x| ≤ r/‖z‖} := by
      ext x
      simp only [mem_ofPred_eq,u,inner_smul_left,conj_trivial,abs_mul,abs_inv,abs_norm]
      rw [inv_mul_eq_div,div_le_div_iff_of_pos_right hn]
    rw [he]
    apply (gaussian_unit_inner_band hu (div_nonneg hr.le hn.le)).trans
    apply ENNReal.ofReal_le_ofReal
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hn hd).mpr
    unfold gaussianVectorBandConstant
    have hh := mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge hz))
      (mul_nonneg hc.le hr.le)
    nlinarith [mul_pos hc (mul_pos hr hn)]

theorem gaussianRows_vector_band (z : Space d) {r : ℝ} (hr : 0 < r) :
    gaussianRows d h {A | ∀ i, |inner ℝ z (A i)| ≤ r} ≤
      ENNReal.ofReal ((gaussianVectorBandConstant*r/(‖z‖+r))^h) := by
  have he : {A : Fin h → Space d | ∀ i, |inner ℝ z (A i)| ≤ r} =
      Set.pi univ (fun _ => {x : Space d | |inner ℝ z x| ≤ r}) := by ext A; simp
  rw [gaussianRows,he,Measure.pi_pi]
  calc
    _ ≤ ∏ _ : Fin h, ENNReal.ofReal (gaussianVectorBandConstant*r/(‖z‖+r)) :=
      Finset.prod_le_prod (fun _ _ => gaussian_vector_band z hr)
    _ = _ := by
      rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin,
        ← ENNReal.ofReal_pow (div_nonneg
          (mul_nonneg gaussianVectorBandConstant_pos.le hr.le) (by positivity))]

end Falconer

end OAI
