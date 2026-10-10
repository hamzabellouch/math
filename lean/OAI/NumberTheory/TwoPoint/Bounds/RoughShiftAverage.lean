import OAI.NumberTheory.TwoPoint.Bounds.WindowPolynomialBounds
import OAI.NumberTheory.TwoPoint.Bounds.RoughShiftBoundary

namespace OAI

/-!
# A finite rough-shift correlation inequality

The three terms are the explicit translation error, the low-frequency
Cauchy--Schwarz term, and the high-frequency fourth-moment term.  Sieve
estimates and MRT scale estimates enter only through their numerical bounds.
-/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

noncomputable def roughShiftProfile (f g : ℕ → ℂ) (Z : Finset ℕ) (h n : ℕ) : ℂ :=
  ∑ z ∈ Z, (z : ℂ)⁻¹ * (f n * g (n + h * z))

noncomputable def roughShiftAverage (f g : ℕ → ℂ) (Z : Finset ℕ) (h Y : ℕ) : ℂ :=
  positivePrefix (roughShiftProfile f g Z h) Y / (Y : ℂ)

lemma norm_roughShiftProfile_le (f g : ℕ → ℂ) (hf : OneBounded f) (hg : OneBounded g)
    (Z : Finset ℕ) (h n : ℕ) (hn : 0 < n) :
    ‖roughShiftProfile f g Z h n‖ ≤ ∑ z ∈ Z, (z : ℝ)⁻¹ := by
  have hh := norm_weightedShiftProfile_le Z (fun z => (z : ℂ)⁻¹)
    (fun z => h * z) f g hf hg 1 0 n hn
  simpa only [weightedShiftProfile, roughShiftProfile, Nat.mod_one, ite_true,
    norm_inv, Complex.norm_natCast] using hh

lemma translated_roughShiftProfile_eq (f g : ℕ → ℂ) (Z : Finset ℕ) (D h Y : ℕ)
    (hZ : ∀ z ∈ Z, z ≤ 2 * D) :
    translatedPrefixAverage (roughShiftProfile f g Z h) Y D =
      (D : ℂ)⁻¹ * ∑ v ∈ range Y, ∫ θ,
        roughFourierPolynomial Z h θ * forwardWindowPolynomial f D (v + 1) θ *
          backwardWindowPolynomial g ((2 * h + 1) * D) (v + 1) θ
            ∂AddCircle.haarAddCircle := by
  unfold translatedPrefixAverage
  congr 1
  calc
    _ = ∑ m ∈ Icc 1 D,
        positivePrefix (fun n => roughShiftProfile f g Z h (n + m)) Y := by
      simpa only [Nat.zero_add] using (sum_Icc_shift
        (fun m => positivePrefix (fun n => roughShiftProfile f g Z h (n + m)) Y) 0 D).symm
    _ = _ := by
      rw [summed_rough_shift_convolution f g Z D h Y hZ]
      rfl

lemma rough_window_energy_sum_bound (f g : ℕ → ℂ) (hf : OneBounded f)
    (hg : OneBounded g) (D Q Y : ℕ) :
    (∑ v ∈ range Y,
      Real.sqrt (∫ θ, ‖forwardWindowPolynomial f D (v + 1) θ‖ ^ 2
        ∂AddCircle.haarAddCircle) *
      Real.sqrt (∫ θ, ‖backwardWindowPolynomial g Q (v + 1) θ‖ ^ 2
        ∂AddCircle.haarAddCircle)) ≤ (Y : ℝ) * (Real.sqrt D * Real.sqrt Q) := by
  calc
    _ ≤ ∑ _v ∈ range Y, Real.sqrt (D : ℝ) * Real.sqrt Q := by
      apply sum_le_sum
      intro v _
      exact mul_le_mul
        (Real.sqrt_le_sqrt (integral_forwardWindowPolynomial_sq_le f hf D (v + 1)))
        (Real.sqrt_le_sqrt (integral_backwardWindowPolynomial_sq_le g hg Q (v + 1)))
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by simp

/-- All Fourier ingredients are now attached to the concrete two windows. -/
theorem rough_convolution_sum_bound (f g : ℕ → ℂ) (hf : OneBounded f)
    (hg : OneBounded g) (Z : Finset ℕ) (D h Y : ℕ)
    (ε U V K : ℝ) (hε : 0 < ε) (hU : 0 ≤ U) (hK : 0 ≤ K)
    (hB : ∀ θ, ‖roughFourierPolynomial Z h θ‖ ≤ U)
    (hV : (∫ θ, ‖roughFourierPolynomial Z h θ‖ ^ 4
      ∂AddCircle.haarAddCircle) ≤ V)
    (hF : ∀ θ, (∑ v ∈ range Y, ‖forwardWindowPolynomial f D (v + 1) θ‖) ≤ K) :
    ‖∑ v ∈ range Y, ∫ θ,
      roughFourierPolynomial Z h θ * forwardWindowPolynomial f D (v + 1) θ *
        backwardWindowPolynomial g ((2 * h + 1) * D) (v + 1) θ
          ∂AddCircle.haarAddCircle‖ ≤
      ε * ((Y : ℝ) * (Real.sqrt D * Real.sqrt ((2 * h + 1) * D))) +
        (U * ((2 * h + 1) * D) * K / ε ^ 4) * V := by
  have hh := fourier_region_bound (range Y) (roughFourierPolynomial Z h)
    (fun v => forwardWindowPolynomial f D (v + 1))
    (fun v => backwardWindowPolynomial g ((2 * h + 1) * D) (v + 1))
    (continuous_fourierPolynomial _ _ _)
    (fun v _ => continuous_forwardWindowPolynomial f D (v + 1))
    (fun v _ => continuous_backwardWindowPolynomial g ((2 * h + 1) * D) (v + 1))
    ε U ((2 * h + 1) * D) K hε hU (by positivity) hK hB
    (fun v _ θ => by
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using
        norm_backwardWindowPolynomial_le g hg ((2 * h + 1) * D) (v + 1) θ) hF
  apply hh.trans
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ hε.le
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using
      rough_window_energy_sum_bound f g hf hg D ((2 * h + 1) * D) Y
  · exact mul_le_mul_of_nonneg_left hV (by positivity)

lemma normalized_translated_roughShift_bound (f g : ℕ → ℂ)
    (Z : Finset ℕ) (D h Y : ℕ) (hD : 0 < D) (hY : 0 < Y)
    (hZ : ∀ z ∈ Z, z ≤ 2 * D) (W : ℝ)
    (hW : ‖∑ v ∈ range Y, ∫ θ,
      roughFourierPolynomial Z h θ * forwardWindowPolynomial f D (v + 1) θ *
        backwardWindowPolynomial g ((2 * h + 1) * D) (v + 1) θ
          ∂AddCircle.haarAddCircle‖ ≤ W) :
    ‖translatedPrefixAverage (roughShiftProfile f g Z h) Y D / (Y : ℂ)‖ ≤
      W / ((Y : ℝ) * D) := by
  rw [translated_roughShiftProfile_eq f g Z D h Y hZ,
    norm_div, norm_mul, norm_inv, Complex.norm_natCast, Complex.norm_natCast]
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hYr : (0 : ℝ) < Y := by exact_mod_cast hY
  calc
    _ ≤ (D : ℝ)⁻¹ * W / Y :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hW (by positivity)) hYr.le
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

/-- The finite correlation bound before inserting the sieve estimates and
the size estimates for the published MRT error. -/
theorem rough_shift_average_bound (f g : ℕ → ℂ) (hf : OneBounded f)
    (hg : OneBounded g) (Z : Finset ℕ) (D h Y : ℕ) (hD : 0 < D) (hY : 0 < Y)
    (hZ : ∀ z ∈ Z, z ≤ 2 * D)
    (ε U V K : ℝ) (hε : 0 < ε) (hU : 0 ≤ U) (hK : 0 ≤ K)
    (hB : ∀ θ, ‖roughFourierPolynomial Z h θ‖ ≤ U)
    (hV : (∫ θ, ‖roughFourierPolynomial Z h θ‖ ^ 4
      ∂AddCircle.haarAddCircle) ≤ V)
    (hF : ∀ θ, (∑ v ∈ range Y, ‖forwardWindowPolynomial f D (v + 1) θ‖) ≤ K) :
    ‖roughShiftAverage f g Z h Y‖ ≤
      2 * (D : ℝ) / Y * (∑ z ∈ Z, (z : ℝ)⁻¹) +
      (ε * ((Y : ℝ) * (Real.sqrt D * Real.sqrt ((2 * h + 1) * D))) +
        (U * ((2 * h + 1) * D) * K / ε ^ 4) * V) / ((Y : ℝ) * D) := by
  let u := roughShiftProfile f g Z h
  have he := norm_normalized_translation_error u Y D hY hD
    (∑ z ∈ Z, (z : ℝ)⁻¹) (sum_nonneg (fun z _ => by positivity))
    (fun n hn => norm_roughShiftProfile_le f g hf hg Z h n hn)
  have hc := normalized_translated_roughShift_bound f g Z D h Y hD hY hZ _
    (rough_convolution_sum_bound f g hf hg Z D h Y ε U V K hε hU hK hB hV hF)
  calc
    ‖roughShiftAverage f g Z h Y‖ = ‖translatedPrefixAverage u Y D / (Y : ℂ) -
        (translatedPrefixAverage u Y D - positivePrefix u Y) / (Y : ℂ)‖ := by
      congr 1
      dsimp [roughShiftAverage, u]
      ring
    _ ≤ ‖translatedPrefixAverage u Y D / (Y : ℂ)‖ +
        ‖(translatedPrefixAverage u Y D - positivePrefix u Y) / (Y : ℂ)‖ := norm_sub_le _ _
    _ ≤ _ := by simpa only [add_comm] using add_le_add hc he

end TwoPointCorrelations

end OAI
