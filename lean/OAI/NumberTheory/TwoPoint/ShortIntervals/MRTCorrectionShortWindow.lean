import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCorrectionSummability
import OAI.NumberTheory.TwoPoint.Bounds.SmoothWindowSum

namespace OAI

/-! Exact short-window convolution and the uniform large-divisor tail
in the reduction to completely multiplicative functions. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma mrt_correction_finite_sum (F : ℕ → ℂ) (hF : Multiplicative F) (hF1 : F 1=1)
    {n B : ℕ} (hn : 0 < n) (hnB : n ≤ B) :
    F n = ∑ d ∈ Icc 1 B,
      mrtCorrection F d*dilationSequence d (mrtCompletePart F) n := by
  rw [mrt_multiplicative_divisor_sum F hF hF1 hn]
  have hsub : n.divisors ⊆ Icc 1 B := by
    intro d hd
    have hdvd := (Nat.mem_divisors.mp hd).1
    exact mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hdvd hn,(Nat.le_of_dvd hn hdvd).trans hnB⟩
  calc
    _ = ∑ d ∈ n.divisors, mrtCorrection F d*dilationSequence d (mrtCompletePart F) n := by
      apply sum_congr rfl
      intro d hd
      simp only [dilationSequence,(Nat.mem_divisors.mp hd).1,ite_true]
    _ = _ := sum_subset hsub (by
      intro d _ hd
      have hnot : ¬d ∣ n := fun h => hd (Nat.mem_divisors.mpr ⟨h,hn.ne'⟩)
      simp only [dilationSequence,hnot,ite_false,mul_zero])

lemma mrt_correction_short_sum_fixed (F : ℕ → ℂ) (hF : Multiplicative F)
    (hF1 : F 1=1) (H v B : ℕ) (hv : v+H ≤ B) (α : ℝ) :
    shortExponentialSum F H α (v:ℕ) =
      ∑ d ∈ Icc 1 B, mrtCorrection F d*
        shortExponentialSum (dilationSequence d (mrtCompletePart F)) H α (v:ℕ) := by
  simp only [shortExponentialSum_at_nat]
  calc
    _ = ∑ n ∈ Icc (v+1) (v+H),
        (∑ d ∈ Icc 1 B, mrtCorrection F d*dilationSequence d (mrtCompletePart F) n)*
          additiveCharacter α n := by
      apply sum_congr rfl
      intro n hn
      rw [mrt_correction_finite_sum F hF hF1
        (by have hh := (mem_Icc.mp hn).1; omega) ((mem_Icc.mp hn).2.trans hv)]
    _ = _ := by
      simp only [sum_mul,mul_sum,mul_assoc]
      rw [sum_comm]

theorem mrt_correction_short_sum (F : ℕ → ℂ) (hF : Multiplicative F)
    (hF1 : F 1=1) (H v : ℕ) (α : ℝ) :
    shortExponentialSum F H α (v:ℕ) =
      ∑ d ∈ Icc 1 (v+H), mrtCorrection F d*
        shortExponentialSum (mrtCompletePart F) ((v+H)/d-v/d) (d*α) (v/d:ℕ) := by
  rw [mrt_correction_short_sum_fixed F hF hF1 H v (v+H) le_rfl α]
  apply sum_congr rfl
  intro d hd
  rw [shortExponentialSum_dilation _ d H v (mem_Icc.mp hd).1 α]

lemma mrt_dilation_prefix_count (d B : ℕ) (hd : 0 < d) :
    (∑ n ∈ range B, if d ∣ n+1 then (1:ℝ) else 0) = (B/d:ℕ) := by
  have he : (∑ n ∈ range B, if d ∣ n+1 then (1:ℝ) else 0) =
      ∑ n ∈ Icc 1 B, if d ∣ n then (1:ℝ) else 0 := by
    apply sum_bij (fun n _ => n+1)
    · intro n hn
      exact mem_Icc.mpr ⟨by omega,by have hh := mem_range.mp hn; omega⟩
    · intro n _ m _ hnm
      omega
    · intro n hn
      obtain ⟨hn1,hnB⟩ := mem_Icc.mp hn
      exact ⟨n-1,mem_range.mpr (by omega),by omega⟩
    · intro n _
      rfl
  rw [he,← sum_filter]
  calc
    _ = ∑ _m ∈ Icc 1 (B/d), (1:ℝ) := by
      symm
      apply sum_bij (fun m _ => d*m)
      · intro m hm
        obtain ⟨hm1,hmB⟩ := mem_Icc.mp hm
        exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hd hm1,
          by simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).mp hmB⟩,
          dvd_mul_right d m⟩
      · intro m _ n _ hmn
        exact Nat.eq_of_mul_eq_mul_left hd hmn
      · intro n hn
        obtain ⟨hnI,hdiv⟩ := mem_filter.mp hn
        obtain ⟨hn1,hnB⟩ := mem_Icc.mp hnI
        exact ⟨n/d,mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hn1 hdiv) hd,
          Nat.div_le_div_right hnB⟩,Nat.mul_div_cancel' hdiv⟩
      · intro _ _
        rfl
    _ = _ := by simp

lemma mrt_dilation_short_integral (G : ℕ → ℂ) (hG : OneBounded G)
    (d X H : ℕ) (hd : 0 < d) (α : ℝ) :
    shortExponentialIntegral (dilationSequence d G) X H α ≤ (H:ℝ)*( (X+H)/d:ℕ) := by
  have hpoint (n : ℕ) (hn : 0 < n) :
      ‖dilationSequence d G n-(0:ℂ)‖ ≤ if d ∣ n then (1:ℝ) else 0 := by
    by_cases hdn : d ∣ n
    · simpa only [dilationSequence,hdn,ite_true,sub_zero] using
        hG (n/d) (Nat.div_pos (Nat.le_of_dvd hn hdn) hd)
    · simp only [dilationSequence,hdn,ite_false,sub_self,norm_zero,le_refl]
  have hz (v : ℕ) : shortWindowSum (fun _ => (0:ℂ)) H α v = 0 := by
    simp only [shortWindowSum,zero_mul,sum_const_zero]
  have he := window_error_from_density (dilationSequence d G) (fun _ => (0:ℂ))
    (fun n => if d ∣ n then (1:ℝ) else 0) (fun _ => by split_ifs <;> positivity)
    hpoint H X α
  rw [mrt_dilation_prefix_count d (X+H) hd] at he
  simpa only [shortExponentialIntegral_eq_sum,norm_shortExponentialSum_eq_window,hz,sub_zero] using he

lemma mrt_correction_integral_sum (F : ℕ → ℂ) (hF : Multiplicative F)
    (hF1 : F 1=1) (X H : ℕ) (α : ℝ) :
    shortExponentialIntegral F X H α ≤
      ∑ d ∈ Icc 1 (X+H), ‖mrtCorrection F d‖*
        shortExponentialIntegral (dilationSequence d (mrtCompletePart F)) X H α := by
  simp only [shortExponentialIntegral_eq_sum]
  calc
    _ ≤ ∑ v ∈ range X, ∑ d ∈ Icc 1 (X+H), ‖mrtCorrection F d‖*
        ‖shortExponentialSum (dilationSequence d (mrtCompletePart F)) H α (v:ℕ)‖ := by
      apply sum_le_sum
      intro v hv
      rw [mrt_correction_short_sum_fixed F hF hF1 H v (X+H)
        (by have hh := mem_range.mp hv; omega) α]
      simpa only [norm_mul] using norm_sum_le (Icc 1 (X+H))
        (fun d => mrtCorrection F d*
          shortExponentialSum (dilationSequence d (mrtCompletePart F)) H α (v:ℕ))
    _ = _ := by rw [sum_comm]; simp only [mul_sum]

theorem mrt_correction_short_integral_tail (F : ℕ → ℂ) (hF : Multiplicative F)
    (hFb : OneBounded F) (hF1 : F 1=1) (X H W : ℕ) (hW : 0 < W)
    (hHX : H ≤ X) (α : ℝ) :
    shortExponentialIntegral F X H α ≤
      (∑ d ∈ (Icc 1 (X+H)).filter (fun d => d ≤ W), ‖mrtCorrection F d‖*
        shortExponentialIntegral (dilationSequence d (mrtCompletePart F)) X H α) +
      2*mrtCorrectionBound*X*H*(W:ℝ)^(-(1/4:ℝ)) := by
  let U := (Icc 1 (X+H)).filter (fun d => ¬d ≤ W)
  have htail : (∑ d ∈ U, ‖mrtCorrection F d‖*
      shortExponentialIntegral (dilationSequence d (mrtCompletePart F)) X H α) ≤
      2*mrtCorrectionBound*X*H*(W:ℝ)^(-(1/4:ℝ)) := by
    have hm := mrt_correction_tail_bound F hFb hF1 hW U
      (fun d hd => by have hh := (mem_filter.mp hd).2; omega)
    calc
      _ ≤ (H:ℝ)*(X+H)*(∑ d ∈ U, ‖mrtCorrection F d‖/(d:ℝ)) := by
        rw [mul_sum]
        apply sum_le_sum
        intro d hd
        have hd0 : 0 < d := (mem_Icc.mp (mem_filter.mp hd).1).1
        have hi := mrt_dilation_short_integral (mrtCompletePart F)
          (mrtCompletePart_oneBounded F hFb) d X H hd0 α
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
        have hh := mul_le_mul_of_nonneg_right hHXr
          (mul_nonneg (Nat.cast_nonneg H) hC)
        nlinarith
  calc
    _ ≤ ∑ d ∈ Icc 1 (X+H), ‖mrtCorrection F d‖*
        shortExponentialIntegral (dilationSequence d (mrtCompletePart F)) X H α :=
      mrt_correction_integral_sum F hF hF1 X H α
    _ = _ + ∑ d ∈ U, ‖mrtCorrection F d‖*
        shortExponentialIntegral (dilationSequence d (mrtCompletePart F)) X H α :=
      (sum_filter_add_sum_filter_not _ (fun d => d ≤ W) _).symm
    _ ≤ _ := add_le_add le_rfl htail

end TwoPointCorrelations

end OAI
