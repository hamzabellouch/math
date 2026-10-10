import OAI.MeasureTheory.Falconer.Slicing.GaussianTripleNormalization

namespace OAI

/-! # A three-band bound that includes singular triples -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

noncomputable def gaussianTripleBandConstant : ℝ :=
  2*gaussianBandConstant^2+8*gaussianVolumeNormalization 3

theorem gaussianTripleBandConstant_pos : 0 < gaussianTripleBandConstant := by
  have hv : 0 < gaussianVolumeNormalization 3 := by
    unfold gaussianVolumeNormalization
    positivity
  unfold gaussianTripleBandConstant
  positivity

theorem gaussian_three_vector_truncated (v : Fin 3 → Space d)
    (hu : ‖v 0‖ = 1) (hv : ‖v 1‖ = 1)
    {r a α : ℝ} (hr : 0 < r) (ha : 0 < a) (ha1 : a ≤ 1)
    (hsep : a ≤ ‖perpendicularPart (v 0) (v 1)‖)
    (hgram : a^2*α ≤ Real.sqrt (Matrix.gram ℝ v).det) :
    stdGaussian (Space d) {x | ∀ j, |inner ℝ (v j) x| ≤ r} ≤
      ENNReal.ofReal (gaussianTripleBandConstant*r^3/(a^2*max α r)) := by
  have hC0 := gaussianTripleBandConstant_pos
  have hC₂ : 2*gaussianBandConstant^2 ≤ gaussianTripleBandConstant := by
    have hp : 0 ≤ gaussianVolumeNormalization 3 := by
      unfold gaussianVolumeNormalization
      positivity
    unfold gaussianTripleBandConstant
    linarith
  have hC₃ : 8*gaussianVolumeNormalization 3 ≤ gaussianTripleBandConstant := by
    unfold gaussianTripleBandConstant
    nlinarith [sq_nonneg gaussianBandConstant]
  by_cases hα : α ≤ r
  · rw [max_eq_right hα]
    have hne : perpendicularPart (v 0) (v 1) ≠ 0 :=
      norm_pos_iff.mp (ha.trans_le hsep)
    have hsub : {x : Space d | ∀ j, |inner ℝ (v j) x| ≤ r} ⊆
        {x : Space d | |inner ℝ (v 0) x| ≤ r ∧ |inner ℝ (v 1) x| ≤ r} := by
      intro x hx
      exact ⟨hx 0,hx 1⟩
    apply ((measure_mono hsub).trans (gaussian_two_band_nondegenerate hu hv hr.le hne)).trans
    apply ENNReal.ofReal_le_ofReal
    have hden : a^2 ≤ ‖perpendicularPart (v 0) (v 1)‖ := by
      have : a^2 ≤ a := by nlinarith
      exact this.trans hsep
    calc
      _ ≤ gaussianTripleBandConstant*r^2/‖perpendicularPart (v 0) (v 1)‖ := by
        gcongr
      _ ≤ gaussianTripleBandConstant*r^2/a^2 := by gcongr
      _ = _ := by field_simp
  · have hαr : r < α := lt_of_not_ge hα
    have hα0 : 0 < α := hr.trans hαr
    have hg : 0 < (Matrix.gram ℝ v).det := by
      have : 0 < Real.sqrt (Matrix.gram ℝ v).det :=
        (mul_pos (sq_pos_of_pos ha) hα0).trans_le hgram
      exact Real.sqrt_pos.mp this
    rw [max_eq_left hαr.le]
    apply (gaussian_three_vector_band v hg hr.le).trans
    apply ENNReal.ofReal_le_ofReal
    calc
      _ = 8*gaussianVolumeNormalization 3*r^3/Real.sqrt (Matrix.gram ℝ v).det := by
        rw [div_eq_mul_inv]
        ring
      _ ≤ gaussianTripleBandConstant*r^3/(a^2*α) := by
        gcongr

theorem gaussianRows_three_vector_truncated (v : Fin 3 → Space d)
    (hu : ‖v 0‖ = 1) (hv : ‖v 1‖ = 1)
    {r a α : ℝ} (hr : 0 < r) (ha : 0 < a) (ha1 : a ≤ 1)
    (hsep : a ≤ ‖perpendicularPart (v 0) (v 1)‖)
    (hgram : a^2*α ≤ Real.sqrt (Matrix.gram ℝ v).det) :
    gaussianRows d h {A | ∀ i, ∀ j, |inner ℝ (v j) (A i)| ≤ r} ≤
      ENNReal.ofReal ((gaussianTripleBandConstant*r^3/(a^2*max α r))^h) := by
  have hC0 := gaussianTripleBandConstant_pos
  have he : {A : Fin h → Space d | ∀ i, ∀ j, |inner ℝ (v j) (A i)| ≤ r} =
      Set.pi univ (fun _ => {x : Space d | ∀ j, |inner ℝ (v j) x| ≤ r}) := by
    ext A
    simp
  rw [gaussianRows,he,Measure.pi_pi]
  calc
    _ ≤ ∏ _ : Fin h, ENNReal.ofReal
        (gaussianTripleBandConstant*r^3/(a^2*max α r)) :=
      Finset.prod_le_prod (fun _ _ => gaussian_three_vector_truncated v hu hv hr ha ha1 hsep hgram)
    _ = _ := by
      rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin,← ENNReal.ofReal_pow]
      positivity

theorem gaussianRows_three_vector_truncated_normalized (v : Fin 3 → Space d)
    (hu : ‖v 0‖ = 1) (hv : ‖v 1‖ = 1)
    {r a α : ℝ} (hr : 0 < r) (ha : 0 < a) (ha1 : a ≤ 1)
    (hsep : a ≤ ‖perpendicularPart (v 0) (v 1)‖)
    (hgram : a^2*α ≤ Real.sqrt (Matrix.gram ℝ v).det) :
    (ENNReal.ofReal (r^(-(h:ℝ))))^3 *
      gaussianRows d h {A | ∀ i, ∀ j, |inner ℝ (v j) (A i)| ≤ r} ≤
      ENNReal.ofReal ((gaussianTripleBandConstant/(a^2*max α r))^h) := by
  apply (mul_le_mul' le_rfl (gaussianRows_three_vector_truncated v hu hv hr ha ha1 hsep hgram)).trans_eq
  have he : gaussianTripleBandConstant*r^3/(a^2*max α r) =
      (gaussianTripleBandConstant/(a^2*max α r))*r^3 := by ring
  rw [he,gaussian_cubed_band_normalization hr]

end Falconer

end OAI
