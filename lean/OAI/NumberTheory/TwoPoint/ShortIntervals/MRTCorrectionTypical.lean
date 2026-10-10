import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCorrectionShortWindow
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTTypicalCoarse

namespace OAI

/-! The prime-power correction preserves the literal typical mask on
small divisors avoiding the selected bands. The remaining divisors are
paid by their absolute reciprocal mass, without removing that mask. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def mrtCorrectionMaskedCofactor {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (d n : ℕ) : ℂ :=
  if mrtTypical J P (d*n) then mrtCompletePart F n else 0

lemma mrt_correction_masked_dilation {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (d n : ℕ) :
    dilationSequence d (mrtCorrectionMaskedCofactor J P F d) n =
      if mrtTypical J P n then dilationSequence d (mrtCompletePart F) n else 0 := by
  unfold dilationSequence mrtCorrectionMaskedCofactor
  by_cases hd : d ∣ n
  · simp only [hd,ite_true,Nat.mul_div_cancel' hd]
  · simp only [hd,ite_false,ite_self]

lemma mrt_correction_masked_oneBounded {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (hF : OneBounded F) (d : ℕ) :
    OneBounded (mrtCorrectionMaskedCofactor J P F d) := by
  intro n hn
  unfold mrtCorrectionMaskedCofactor
  split_ifs
  · exact mrtCompletePart_oneBounded F hF n hn
  · simp

lemma mrt_correction_masked_of_avoids {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (F : ℕ → ℂ) {d : ℕ} (hd : mrtPrimeAvoids (J.biUnion P) d) :
    mrtCorrectionMaskedCofactor J P F d = mrtTypicalCoefficient J P (mrtCompletePart F) := by
  funext n
  unfold mrtCorrectionMaskedCofactor mrtTypicalCoefficient
  rw [mrtTypical_mul_of_avoids J P hP hd n]

lemma mrt_correction_typical_finite {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (hF : Multiplicative F) (hF1 : F 1=1)
    {n B : ℕ} (hn : 0 < n) (hnB : n ≤ B) :
    mrtTypicalCoefficient J P F n = ∑ d ∈ Icc 1 B, mrtCorrection F d*
      dilationSequence d (mrtCorrectionMaskedCofactor J P F d) n := by
  simp only [mrt_correction_masked_dilation]
  unfold mrtTypicalCoefficient
  by_cases ht : mrtTypical J P n
  · simpa only [ht,ite_true] using mrt_correction_finite_sum F hF hF1 hn hnB
  · simp only [ht,ite_false,mul_zero,sum_const_zero]

theorem mrt_correction_typical_short_sum {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (hF : Multiplicative F) (hF1 : F 1=1)
    (H v B : ℕ) (hv : v+H ≤ B) (α : ℝ) :
    shortExponentialSum (mrtTypicalCoefficient J P F) H α (v:ℕ) =
      ∑ d ∈ Icc 1 B, mrtCorrection F d*
        shortExponentialSum (dilationSequence d (mrtCorrectionMaskedCofactor J P F d))
          H α (v:ℕ) := by
  simp only [shortExponentialSum_at_nat]
  calc
    _ = ∑ n ∈ Icc (v+1) (v+H),
        (∑ d ∈ Icc 1 B, mrtCorrection F d*
          dilationSequence d (mrtCorrectionMaskedCofactor J P F d) n)*additiveCharacter α n := by
      apply sum_congr rfl
      intro n hn
      rw [mrt_correction_typical_finite J P F hF hF1
        (by have hh := (mem_Icc.mp hn).1; omega) ((mem_Icc.mp hn).2.trans hv)]
    _ = _ := by
      simp only [sum_mul,mul_sum,mul_assoc]
      rw [sum_comm]

lemma mrt_correction_typical_integral_sum {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (hF : Multiplicative F) (hF1 : F 1=1)
    (X H : ℕ) (α : ℝ) :
    shortExponentialIntegral (mrtTypicalCoefficient J P F) X H α ≤
      ∑ d ∈ Icc 1 (X+H), ‖mrtCorrection F d‖*
        shortExponentialIntegral
          (dilationSequence d (mrtCorrectionMaskedCofactor J P F d)) X H α := by
  simp only [shortExponentialIntegral_eq_sum]
  calc
    _ ≤ ∑ v ∈ range X, ∑ d ∈ Icc 1 (X+H), ‖mrtCorrection F d‖*
        ‖shortExponentialSum (dilationSequence d (mrtCorrectionMaskedCofactor J P F d))
          H α (v:ℕ)‖ := by
      apply sum_le_sum
      intro v hv
      rw [mrt_correction_typical_short_sum J P F hF hF1 H v (X+H)
        (by have hh := mem_range.mp hv; omega) α]
      simpa only [norm_mul] using norm_sum_le (Icc 1 (X+H))
        (fun d => mrtCorrection F d*shortExponentialSum
          (dilationSequence d (mrtCorrectionMaskedCofactor J P F d)) H α (v:ℕ))
    _ = _ := by rw [sum_comm]; simp only [mul_sum]

theorem mrt_correction_typical_tail {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (F : ℕ → ℂ) (hF : Multiplicative F) (hFb : OneBounded F) (hF1 : F 1=1)
    (X H W : ℕ) (hW : 0 < W) (hHX : H ≤ X)
    (havoid : ∀ d : ℕ, 0 < d → d ≤ W → mrtPrimeAvoids (J.biUnion P) d)
    (α : ℝ) :
    shortExponentialIntegral (mrtTypicalCoefficient J P F) X H α ≤
      (∑ d ∈ (Icc 1 (X+H)).filter (fun d => d ≤ W), ‖mrtCorrection F d‖*
        shortExponentialIntegral
          (dilationSequence d (mrtTypicalCoefficient J P (mrtCompletePart F))) X H α) +
      2*mrtCorrectionBound*X*H*(W:ℝ)^(-(1/4:ℝ)) := by
  let U := (Icc 1 (X+H)).filter (fun d => ¬d ≤ W)
  have htail : (∑ d ∈ U, ‖mrtCorrection F d‖*
      shortExponentialIntegral (dilationSequence d (mrtCorrectionMaskedCofactor J P F d)) X H α) ≤
      2*mrtCorrectionBound*X*H*(W:ℝ)^(-(1/4:ℝ)) := by
    have hm := mrt_correction_tail_bound F hFb hF1 hW U
      (fun d hd => by have hh := (mem_filter.mp hd).2; omega)
    calc
      _ ≤ (H:ℝ)*(X+H)*(∑ d ∈ U, ‖mrtCorrection F d‖/(d:ℝ)) := by
        rw [mul_sum]
        apply sum_le_sum
        intro d hd
        have hd0 : 0 < d := (mem_Icc.mp (mem_filter.mp hd).1).1
        have hi := mrt_dilation_short_integral (mrtCorrectionMaskedCofactor J P F d)
          (mrt_correction_masked_oneBounded J P F hFb d) d X H hd0 α
        calc
          _ ≤ ‖mrtCorrection F d‖*((H:ℝ)*((X+H)/d:ℕ)) :=
            mul_le_mul_of_nonneg_left hi (norm_nonneg _)
          _ ≤ ‖mrtCorrection F d‖*((H:ℝ)*((X+H:ℕ):ℝ)/(d:ℝ)) := by
            have hh₀ : (((X+H)/d:ℕ):ℝ) ≤ ((X+H:ℕ):ℝ)/(d:ℝ) := Nat.cast_div_le
            have hh : (H:ℝ)*((X+H)/d:ℕ) ≤ (H:ℝ)*(((X+H:ℕ):ℝ)/(d:ℝ)) :=
              mul_le_mul_of_nonneg_left hh₀ (Nat.cast_nonneg H)
            simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hh (norm_nonneg (mrtCorrection F d))
          _ = _ := by push_cast; ring
      _ ≤ (H:ℝ)*(X+H)*(mrtCorrectionBound*(W:ℝ)^(-(1/4:ℝ))) :=
        mul_le_mul_of_nonneg_left hm (by positivity)
      _ ≤ _ := by
        have hHXr : (H:ℝ) ≤ X := by exact_mod_cast hHX
        have hC : 0 ≤ mrtCorrectionBound*(W:ℝ)^(-(1/4:ℝ)) := by
          unfold mrtCorrectionBound
          positivity
        have hh := mul_le_mul_of_nonneg_right hHXr (mul_nonneg (Nat.cast_nonneg H) hC)
        nlinarith
  have hsmall : (∑ d ∈ (Icc 1 (X+H)).filter (fun d => d ≤ W), ‖mrtCorrection F d‖*
      shortExponentialIntegral (dilationSequence d (mrtCorrectionMaskedCofactor J P F d)) X H α) =
      ∑ d ∈ (Icc 1 (X+H)).filter (fun d => d ≤ W), ‖mrtCorrection F d‖*
        shortExponentialIntegral
          (dilationSequence d (mrtTypicalCoefficient J P (mrtCompletePart F))) X H α := by
    apply sum_congr rfl
    intro d hd
    obtain ⟨hdI,hdW⟩ := mem_filter.mp hd
    rw [mrt_correction_masked_of_avoids J P hP F (havoid d (mem_Icc.mp hdI).1 hdW)]
  calc
    _ ≤ ∑ d ∈ Icc 1 (X+H), ‖mrtCorrection F d‖*
        shortExponentialIntegral (dilationSequence d (mrtCorrectionMaskedCofactor J P F d)) X H α :=
      mrt_correction_typical_integral_sum J P F hF hF1 X H α
    _ = _ + ∑ d ∈ U, ‖mrtCorrection F d‖*
        shortExponentialIntegral (dilationSequence d (mrtCorrectionMaskedCofactor J P F d)) X H α :=
      (sum_filter_add_sum_filter_not _ (fun d => d ≤ W) _).symm
    _ ≤ _ := by rw [hsmall]; exact add_le_add le_rfl htail

theorem mrt_correction_typical_tail_below_primes {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (F : ℕ → ℂ) (hF : Multiplicative F) (hFb : OneBounded F) (hF1 : F 1=1)
    (X H W : ℕ) (hW : 0 < W) (hHX : H ≤ X)
    (hlarge : ∀ j ∈ J, ∀ p ∈ P j, W < p) (α : ℝ) :
    shortExponentialIntegral (mrtTypicalCoefficient J P F) X H α ≤
      (∑ d ∈ (Icc 1 (X+H)).filter (fun d => d ≤ W), ‖mrtCorrection F d‖*
        shortExponentialIntegral
          (dilationSequence d (mrtTypicalCoefficient J P (mrtCompletePart F))) X H α) +
      2*mrtCorrectionBound*X*H*(W:ℝ)^(-(1/4:ℝ)) := by
  apply mrt_correction_typical_tail J P hP F hF hFb hF1 X H W hW hHX _ α
  intro d hd hdW
  apply mrtPrimeAvoids_of_lt _ hd
  intro p hp
  obtain ⟨j,hj,hp⟩ := mem_biUnion.mp hp
  exact hdW.trans_lt (hlarge j hj p hp)

end TwoPointCorrelations

end OAI
