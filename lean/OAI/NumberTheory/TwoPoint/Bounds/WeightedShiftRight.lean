import OAI.NumberTheory.TwoPoint.Bounds.WeightedShiftParameters

namespace OAI

/-! The same finite Fourier argument when the nonpretentious function is
in the second factor. No supremum is moved inside a sum over origins. -/

namespace TwoPointCorrelations

open Finset Filter MeasureTheory
open scoped Classical

lemma backwardWindowPolynomial_eq_forward_neg (g : ℕ → ℂ) (Q v : ℕ)
    (θ : AddCircle (1 : ℝ)) :
    backwardWindowPolynomial g Q v θ = forwardWindowPolynomial g Q v (-θ) := by
  simp only [backwardWindowPolynomial, forwardWindowPolynomial, fourierPolynomial,
    fourier_apply, smul_neg, neg_smul]

theorem weighted_rough_convolution_sum_bound_right (f g : ℕ → ℂ) (hf : OneBounded f)
    (hg : OneBounded g) (Z : Finset ℕ) (c : ℕ → ℂ) (D h Y : ℕ)
    (ε U V K : ℝ) (hε : 0 < ε) (hU : 0 ≤ U) (hK : 0 ≤ K)
    (hB : ∀ θ, ‖weightedRoughFourier Z c h θ‖ ≤ U)
    (hV : (∫ θ, ‖weightedRoughFourier Z c h θ‖ ^ 4
      ∂AddCircle.haarAddCircle) ≤ V)
    (hG : ∀ θ, (∑ v ∈ range Y,
      ‖backwardWindowPolynomial g ((2 * h + 1) * D) (v + 1) θ‖) ≤ K) :
    ‖∑ v ∈ range Y, ∫ θ,
      weightedRoughFourier Z c h θ * forwardWindowPolynomial f D (v + 1) θ *
        backwardWindowPolynomial g ((2 * h + 1) * D) (v + 1) θ
          ∂AddCircle.haarAddCircle‖ ≤
      ε * ((Y : ℝ) * (Real.sqrt D * Real.sqrt ((2 * h + 1) * D))) +
        (U * D * K / ε ^ 4) * V := by
  have he : (∑ v ∈ range Y, ∫ θ,
      weightedRoughFourier Z c h θ * forwardWindowPolynomial f D (v + 1) θ *
        backwardWindowPolynomial g ((2 * h + 1) * D) (v + 1) θ
          ∂AddCircle.haarAddCircle) =
      ∑ v ∈ range Y, ∫ θ,
        weightedRoughFourier Z c h θ * backwardWindowPolynomial g ((2 * h + 1) * D) (v + 1) θ *
          forwardWindowPolynomial f D (v + 1) θ ∂AddCircle.haarAddCircle := by
    apply sum_congr rfl
    intro v _
    apply integral_congr_ae
    exact Eventually.of_forall (fun θ => by ring)
  rw [he]
  have hh := fourier_region_bound (range Y) (weightedRoughFourier Z c h)
    (fun v => backwardWindowPolynomial g ((2 * h + 1) * D) (v + 1))
    (fun v => forwardWindowPolynomial f D (v + 1))
    (continuous_fourierPolynomial _ _ _)
    (fun v _ => continuous_backwardWindowPolynomial g ((2 * h + 1) * D) (v + 1))
    (fun v _ => continuous_forwardWindowPolynomial f D (v + 1))
    ε U D K hε hU (by positivity) hK hB
    (fun v _ θ => norm_forwardWindowPolynomial_le f hf D (v + 1) θ) hG
  apply hh.trans
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ hε.le
    calc
      _ = ∑ v ∈ range Y,
          Real.sqrt (∫ θ, ‖forwardWindowPolynomial f D (v + 1) θ‖ ^ 2
            ∂AddCircle.haarAddCircle) *
          Real.sqrt (∫ θ, ‖backwardWindowPolynomial g ((2 * h + 1) * D) (v + 1) θ‖ ^ 2
            ∂AddCircle.haarAddCircle) := sum_congr rfl (fun _ _ => mul_comm _ _)
      _ ≤ _ := by
        simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using
          rough_window_energy_sum_bound f g hf hg D ((2 * h + 1) * D) Y
  · exact mul_le_mul_of_nonneg_left hV (by positivity)

/-- The second-factor version of the complete finite three-term bound. -/
theorem weighted_rough_shift_average_bound_right (f g : ℕ → ℂ) (hf : OneBounded f)
    (hg : OneBounded g) (Z : Finset ℕ) (c : ℕ → ℂ) (D h Y : ℕ) (hD : 0 < D) (hY : 0 < Y)
    (hZ : ∀ z ∈ Z, z ≤ 2 * D)
    (ε U V K : ℝ) (hε : 0 < ε) (hU : 0 ≤ U) (hK : 0 ≤ K)
    (hB : ∀ θ, ‖weightedRoughFourier Z c h θ‖ ≤ U)
    (hV : (∫ θ, ‖weightedRoughFourier Z c h θ‖ ^ 4
      ∂AddCircle.haarAddCircle) ≤ V)
    (hG : ∀ θ, (∑ v ∈ range Y,
      ‖backwardWindowPolynomial g ((2 * h + 1) * D) (v + 1) θ‖) ≤ K) :
    ‖weightedRoughShiftAverage f g Z c h Y‖ ≤
      2 * (D : ℝ) / Y * (∑ z ∈ Z, ‖c z / (z : ℂ)‖) +
      (ε * ((Y : ℝ) * (Real.sqrt D * Real.sqrt ((2 * h + 1) * D))) +
        (U * D * K / ε ^ 4) * V) / ((Y : ℝ) * D) := by
  let u := weightedRoughShiftProfile f g Z c h
  have he := norm_normalized_translation_error u Y D hY hD
    (∑ z ∈ Z, ‖c z / (z : ℂ)‖) (sum_nonneg (fun _ _ => by positivity))
    (fun n hn => norm_weightedRoughShiftProfile_le f g hf hg Z c h n hn)
  have hc := normalized_translated_weightedRoughShift_bound f g Z c D h Y hD hY hZ _
    (weighted_rough_convolution_sum_bound_right f g hf hg Z c D h Y ε U V K hε hU hK hB hV hG)
  calc
    _ = ‖translatedPrefixAverage u Y D / (Y : ℂ) -
        (translatedPrefixAverage u Y D - positivePrefix u Y) / (Y : ℂ)‖ := by
      congr 1
      dsimp [weightedRoughShiftAverage, u]
      ring
    _ ≤ ‖translatedPrefixAverage u Y D / (Y : ℂ)‖ +
        ‖(translatedPrefixAverage u Y D - positivePrefix u Y) / (Y : ℂ)‖ := norm_sub_le _ _
    _ ≤ _ := by simpa only [add_comm] using add_le_add hc he

/-- The sixth-power condition has the same exponent for either factor. -/
theorem weighted_rough_shift_parameter_bound_right (f g : ℕ → ℂ) (hf : OneBounded f)
    (hg : OneBounded g) (Z : Finset ℕ) (c : ℕ → ℂ) (D h Y : ℕ)
    (hD : 0 < D) (hY : 0 < Y) (hZ : ∀ z ∈ Z, z ≤ 2 * D)
    (q η U V K : ℝ) (hq : 0 ≤ q) (hη : 0 < η)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hK : 0 ≤ K)
    (hmass : (∑ z ∈ Z, ‖c z / (z : ℂ)‖) ≤ 1)
    (hendpoint : (D : ℝ) / Y ≤ η) (hgap : q ^ 6 ≤ η ^ 5)
    (hB : ∀ θ, ‖weightedRoughFourier Z c h θ‖ ≤ U * q)
    (hfourth : (∫ θ, ‖weightedRoughFourier Z c h θ‖ ^ 4
      ∂AddCircle.haarAddCircle) ≤ V / D * q ^ 4)
    (hG : ∀ θ, (∑ v ∈ range Y,
      ‖backwardWindowPolynomial g ((2 * h + 1) * D) (v + 1) θ‖) ≤
      K * Y * ((2 * (h : ℝ) + 1) * D) * q) :
    ‖weightedRoughShiftAverage f g Z c h Y‖ ≤
      (2 + (2 * (h : ℝ) + 1) + (2 * (h : ℝ) + 1) * U * V * K) * η := by
  have he : 2 * (D : ℝ) / Y * (∑ z ∈ Z, ‖c z / (z : ℂ)‖) ≤ 2 * η := by
    calc
      _ = 2 * ((D : ℝ) / Y) * (∑ z ∈ Z, ‖c z / (z : ℂ)‖) := by ring
      _ ≤ 2 * η * 1 := mul_le_mul
        (mul_le_mul_of_nonneg_left hendpoint (by norm_num)) hmass
        (sum_nonneg (fun _ _ => norm_nonneg _)) (by positivity)
      _ = _ := mul_one _
  have hraw := weighted_rough_shift_average_bound_right f g hf hg Z c D h Y hD hY hZ
    η (U * q) (V / D * q ^ 4) (K * Y * ((2 * (h : ℝ) + 1) * D) * q)
    hη (by positivity) (by positivity) hB hfourth hG
  have hlow := rough_low_term_bound D h Y hD hY η hη.le
  have hhigh : (((U * q) * D * (K * Y * ((2 * (h : ℝ) + 1) * D) * q) / η ^ 4) *
      (V / D * q ^ 4)) / ((Y : ℝ) * D) =
      ((2 * (h : ℝ) + 1) * U * V * K) * (q ^ 6 / η ^ 4) := by
    convert weighted_shift_high_identity D h Y hD hY q η U V K hη using 1
    ring
  have hfrac : q ^ 6 / η ^ 4 ≤ η := by
    apply (div_le_iff₀ (pow_pos hη 4)).mpr
    convert hgap using 1
    ring
  have ht := mul_le_mul_of_nonneg_left hfrac
    (show 0 ≤ (2 * (h : ℝ) + 1) * U * V * K by positivity)
  apply hraw.trans
  rw [add_div, hhigh]
  nlinarith only [he, hlow, ht]

end TwoPointCorrelations

end OAI
