import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCorrectionTypical

namespace OAI

/-! The small-divisor terms in the general-multiplicative correction use
literal divided origin ranges, divided window lengths, and dilated additive
frequencies. The rounding cost is one term per original origin. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem mrt_dilation_integral_quotient (G : ℕ → ℂ) (hG : OneBounded G)
    (d X H : ℕ) (hd : 0 < d) (α : ℝ) :
    shortExponentialIntegral (dilationSequence d G) X H α ≤
      (d : ℝ) * shortExponentialIntegral G (X / d + 1) (H / d + 1) (d * α) + X := by
  rw [shortExponentialIntegral_eq_sum]
  calc
    _ ≤ ∑ v ∈ range X, (‖shortWindowSum G (H / d + 1) (d * α) (v / d)‖ + 1) := by
      apply sum_le_sum
      intro v _
      exact norm_shortExponentialSum_dilation_le G hG d H v hd α
    _ = (∑ v ∈ range X, ‖shortWindowSum G (H / d + 1) (d * α) (v / d)‖) + X := by
      rw [sum_add_distrib]
      simp
    _ ≤ (d : ℝ) * (∑ m ∈ range (X / d + 1),
        ‖shortWindowSum G (H / d + 1) (d * α) m‖) + X :=
      add_le_add (quotient_sample_sum_le _ (fun _ => norm_nonneg _) d X hd) le_rfl
    _ = _ := by
      rw [shortExponentialIntegral_eq_sum]
      simp_rw [norm_shortExponentialSum_eq_window]

theorem mrt_correction_quotient_tail (F : ℕ → ℂ) (hF : Multiplicative F)
    (hFb : OneBounded F) (hF1 : F 1 = 1) (X H W : ℕ) (hW : 0 < W)
    (hHX : H ≤ X) (α : ℝ) :
    shortExponentialIntegral F X H α ≤
      (∑ d ∈ (Icc 1 (X + H)).filter (fun d => d ≤ W), ‖mrtCorrection F d‖ *
        ((d : ℝ) * shortExponentialIntegral (mrtCompletePart F)
          (X / d + 1) (H / d + 1) (d * α) + X)) +
      2 * mrtCorrectionBound * X * H * (W : ℝ) ^ (-(1 / 4 : ℝ)) := by
  apply (mrt_correction_short_integral_tail F hF hFb hF1 X H W hW hHX α).trans
  apply add_le_add _ le_rfl
  apply sum_le_sum
  intro d hd
  exact mul_le_mul_of_nonneg_left
    (mrt_dilation_integral_quotient (mrtCompletePart F)
      (mrtCompletePart_oneBounded F hFb) d X H (mem_Icc.mp (mem_filter.mp hd).1).1 α)
    (norm_nonneg _)

theorem mrt_correction_typical_quotient_tail {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (F : ℕ → ℂ) (hF : Multiplicative F) (hFb : OneBounded F) (hF1 : F 1 = 1)
    (X H W : ℕ) (hW : 0 < W) (hHX : H ≤ X)
    (hlarge : ∀ j ∈ J, ∀ p ∈ P j, W < p) (α : ℝ) :
    shortExponentialIntegral (mrtTypicalCoefficient J P F) X H α ≤
      (∑ d ∈ (Icc 1 (X + H)).filter (fun d => d ≤ W), ‖mrtCorrection F d‖ *
        ((d : ℝ) * shortExponentialIntegral (mrtTypicalCoefficient J P (mrtCompletePart F))
          (X / d + 1) (H / d + 1) (d * α) + X)) +
      2 * mrtCorrectionBound * X * H * (W : ℝ) ^ (-(1 / 4 : ℝ)) := by
  apply (mrt_correction_typical_tail_below_primes J P hP F hF hFb hF1
    X H W hW hHX hlarge α).trans
  apply add_le_add _ le_rfl
  apply sum_le_sum
  intro d hd
  exact mul_le_mul_of_nonneg_left
    (mrt_dilation_integral_quotient (mrtTypicalCoefficient J P (mrtCompletePart F))
      (mrtTypicalCoefficient_oneBounded J P _ (mrtCompletePart_oneBounded F hFb))
      d X H (mem_Icc.mp (mem_filter.mp hd).1).1 α) (norm_nonneg _)

lemma mrt_quotient_length_le_two {d A : ℕ} (hd : 0 < d) (hdA : d ≤ A) :
    ((A / d + 1 : ℕ) : ℝ) ≤ 2 * ((A : ℝ) / d) := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hratio : (1 : ℝ) ≤ (A : ℝ) / d :=
    (le_div_iff₀ hdr).mpr (by simpa only [one_mul] using (show (d : ℝ) ≤ A by exact_mod_cast hdA))
  have hdiv : ((A / d : ℕ) : ℝ) ≤ (A : ℝ) / d := Nat.cast_div_le
  simp only [Nat.cast_add, Nat.cast_one]
  linarith

lemma mrt_small_correction_quotient_bound (F G : ℕ → ℂ)
    (hFb : OneBounded F) (hF1 : F 1 = 1) (X H W : ℕ)
    (hWH : W ≤ H) (hHX : H ≤ X) (α ε : ℝ) (hε : 0 ≤ ε)
    (hmean : ∀ d ∈ (Icc 1 (X + H)).filter (fun d => d ≤ W),
      shortExponentialIntegral G (X / d + 1) (H / d + 1) (d * α) ≤
        ε * (X / d + 1 : ℕ) * (H / d + 1 : ℕ)) :
    (∑ d ∈ (Icc 1 (X + H)).filter (fun d => d ≤ W), ‖mrtCorrection F d‖ *
      ((d : ℝ) * shortExponentialIntegral G (X / d + 1) (H / d + 1) (d * α) + X)) ≤
      mrtCorrectionBound * ((4 * ε * X * H) + (W : ℝ) * X) := by
  let S := (Icc 1 (X + H)).filter (fun d => d ≤ W)
  have hmass : (∑ d ∈ S, ‖mrtCorrection F d‖ / (d : ℝ)) ≤ mrtCorrectionBound := by
    simpa only [Nat.cast_one, Real.one_rpow, mul_one] using
      mrt_correction_tail_bound F hFb hF1 (W := 1) (by omega) S
        (fun d hd => (mem_Icc.mp (mem_filter.mp hd).1).1)
  have hsum : (∑ d ∈ S, ‖mrtCorrection F d‖ *
      ((d : ℝ) * shortExponentialIntegral G (X / d + 1) (H / d + 1) (d * α) + X)) ≤
      ((4 * ε * X * H) + (W : ℝ) * X) *
        (∑ d ∈ S, ‖mrtCorrection F d‖ / (d : ℝ)) := by
    rw [mul_sum]
    apply sum_le_sum
    intro d hd
    obtain ⟨hdI, hdW⟩ := mem_filter.mp hd
    have hd0 : 0 < d := (mem_Icc.mp hdI).1
    have hdr : (0 : ℝ) < d := by exact_mod_cast hd0
    have hdH : d ≤ H := hdW.trans hWH
    have hdX : d ≤ X := hdH.trans hHX
    have hx := mrt_quotient_length_le_two hd0 hdX
    have hh := mrt_quotient_length_le_two hd0 hdH
    have hprod : ε * (X / d + 1 : ℕ) * (H / d + 1 : ℕ) ≤
        ε * (2 * ((X : ℝ) / d)) * (2 * ((H : ℝ) / d)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hx hε
      · exact hh
      · positivity
      · positivity
    have hi : (d : ℝ) * shortExponentialIntegral G
        (X / d + 1) (H / d + 1) (d * α) ≤ (4 * ε * X * H) / d := by
      calc
        _ ≤ (d : ℝ) * (ε * (2 * ((X : ℝ) / d)) * (2 * ((H : ℝ) / d))) :=
          mul_le_mul_of_nonneg_left ((hmean d hd).trans hprod) hdr.le
        _ = _ := by field_simp; ring
    have he : (X : ℝ) ≤ ((W : ℝ) * X) / d := by
      apply (le_div_iff₀ hdr).mpr
      have hdWr : (d : ℝ) ≤ W := by exact_mod_cast hdW
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hdWr (Nat.cast_nonneg X)
    calc
      _ ≤ ‖mrtCorrection F d‖ * ((4 * ε * X * H) / d + ((W : ℝ) * X) / d) :=
        mul_le_mul_of_nonneg_left (add_le_add hi he) (norm_nonneg _)
      _ = _ := by ring
  apply hsum.trans
  calc
    _ ≤ ((4 * ε * X * H) + (W : ℝ) * X) * mrtCorrectionBound :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := mul_comm _ _

/-- A uniform divided-window estimate transfers to the original typical
coefficient with an absolute correction constant and explicit rounding loss. -/
theorem mrt_correction_typical_quotient_mean {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (F : ℕ → ℂ) (hF : Multiplicative F) (hFb : OneBounded F) (hF1 : F 1 = 1)
    (X H W : ℕ) (hW : 0 < W) (hWH : W ≤ H) (hHX : H ≤ X)
    (hlarge : ∀ j ∈ J, ∀ p ∈ P j, W < p) (α ε : ℝ) (hε : 0 ≤ ε)
    (hmean : ∀ d ∈ (Icc 1 (X + H)).filter (fun d => d ≤ W),
      shortExponentialIntegral (mrtTypicalCoefficient J P (mrtCompletePart F))
        (X / d + 1) (H / d + 1) (d * α) ≤ ε * (X / d + 1 : ℕ) * (H / d + 1 : ℕ)) :
    shortExponentialIntegral (mrtTypicalCoefficient J P F) X H α ≤
      mrtCorrectionBound * X * H *
        (4 * ε + (W : ℝ) / H + 2 * (W : ℝ) ^ (-(1 / 4 : ℝ))) := by
  have hs := mrt_small_correction_quotient_bound F
    (mrtTypicalCoefficient J P (mrtCompletePart F)) hFb hF1
    X H W hWH hHX α ε hε hmean
  have hH0 : (H : ℝ) ≠ 0 := by exact_mod_cast (hW.trans_le hWH).ne'
  calc
    _ ≤ _ := mrt_correction_typical_quotient_tail J P hP F hF hFb hF1
      X H W hW hHX hlarge α
    _ ≤ mrtCorrectionBound * ((4 * ε * X * H) + (W : ℝ) * X) +
        2 * mrtCorrectionBound * X * H * (W : ℝ) ^ (-(1 / 4 : ℝ)) :=
      add_le_add hs le_rfl
    _ = _ := by field_simp

end TwoPointCorrelations

end OAI
