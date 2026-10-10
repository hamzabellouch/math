import OAI.NumberTheory.TwoPoint.Bounds.DilatedWindows
import OAI.NumberTheory.TwoPoint.Bounds.SmoothTailDensity

namespace OAI

/-! The exact smooth-divisor decomposition inside a short Fourier window,
with the discarded tail bounded before any cancellation is used. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma shortWindowSum_sub (f g : ℕ → ℂ) (D v : ℕ) (α : ℝ) :
    shortWindowSum (fun n => f n - g n) D α v =
      shortWindowSum f D α v - shortWindowSum g D α v := by
  simp only [shortWindowSum, sub_mul, sum_sub_distrib]

lemma norm_shortWindowSum_le (f : ℕ → ℂ) (D v : ℕ) (α : ℝ) :
    ‖shortWindowSum f D α v‖ ≤ ∑ m ∈ range D, ‖f (v + m + 1)‖ := by
  apply (norm_sum_le _ _).trans
  simp only [norm_mul, norm_additiveCharacter, mul_one, le_refl]

lemma window_error_from_density (f g : ℕ → ℂ) (e : ℕ → ℝ)
    (he : ∀ n, 0 ≤ e n) (hfg : ∀ n, 0 < n → ‖f n - g n‖ ≤ e n)
    (D Y : ℕ) (α : ℝ) :
    (∑ v ∈ range Y, ‖shortWindowSum f D α v - shortWindowSum g D α v‖) ≤
      (D : ℝ) * ∑ n ∈ range (Y + D), e (n + 1) := by
  calc
    _ ≤ ∑ v ∈ range Y, ∑ m ∈ range D, e (v + m + 1) := by
      apply sum_le_sum
      intro v _
      rw [← shortWindowSum_sub]
      exact (norm_shortWindowSum_le _ _ _ _).trans
        (sum_le_sum (fun m _ => hfg _ (by omega)))
    _ = ∑ m ∈ range D, ∑ v ∈ range Y, e (v + m + 1) := sum_comm
    _ ≤ ∑ _m ∈ range D, ∑ n ∈ range (Y + D), e (n + 1) := by
      apply sum_le_sum
      intro m hm
      apply sum_le_sum_of_injOn (fun v => v + m)
      · intro v _ w _ h
        change v + m = w + m at h
        omega
      · intro x hx
        obtain ⟨v, hv, rfl⟩ := mem_image.mp hx
        simp only [mem_range] at hm hv ⊢
        omega
      · intro v _
        exact le_rfl
      · intro n _ _
        exact he _
    _ = _ := by simp

lemma truncated_window_error {f : ℕ → ℂ} (hf : OneBounded f)
    (q K D Y : ℕ) (hq : 0 < q) (hK : 0 < K) (α : ℝ) :
    (∑ v ∈ range Y, ‖shortWindowSum (fun n => f (q * n)) D α v -
      shortWindowSum (truncatedDilation q f K) D α v‖) ≤
      (D : ℝ) * (Y + D) * (K : ℝ) ^ (-(1 / 2) : ℝ) *
        smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ) := by
  apply (window_error_from_density _ _
    (fun n => if K < primeSmoothPart q.primeFactors n then 1 else 0)
    (fun _ => by split_ifs <;> positivity)
    (fun n hn => norm_truncatedDilation_error hf q n K hq hn) D Y α).trans
  have hb := smooth_part_tail_density q K (Y + D) hK
  calc
    _ ≤ (D : ℝ) * ((Y + D : ℕ) * (K : ℝ) ^ (-(1 / 2) : ℝ) *
        smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg D)
    _ = _ := by push_cast; ring

lemma smoothDilationTerm_as_dilation (q a : ℕ) (f : ℕ → ℂ)
    (ha : a.primeFactors ⊆ q.primeFactors) :
    smoothDilationTerm q f a = fun n =>
      f (q * a) * dilationSequence a (coprimeRestriction q f) n := by
  funext n
  unfold smoothDilationTerm dilationSequence
  by_cases hd : a ∣ n
  · rw [ite_eq_left ⟨ha, hd⟩, ite_eq_left hd]
  · rw [ite_eq_right (fun h => hd h.2), ite_eq_right hd, mul_zero]

lemma truncated_shortWindowSum {f : ℕ → ℂ} (hf : Multiplicative f)
    (q K D v : ℕ) (hq : 0 < q) (α : ℝ) :
    shortWindowSum (truncatedDilation q f K) D α v =
      ∑ a ∈ (Icc 1 K).filter (fun a => a.primeFactors ⊆ q.primeFactors),
        f (q * a) * shortWindowSum (dilationSequence a (coprimeRestriction q f)) D α v := by
  unfold shortWindowSum
  have hexpand : (∑ m ∈ range D,
      truncatedDilation q f K (v + m + 1) * additiveCharacter α (m + 1)) =
      ∑ m ∈ range D, (∑ a ∈ Icc 1 K,
        smoothDilationTerm q f a (v + m + 1)) * additiveCharacter α (m + 1) := by
    apply sum_congr rfl
    intro m _
    rw [truncatedDilation_eq_sum hf q (v + m + 1) K hq (by omega)]
  rw [hexpand]
  simp_rw [sum_mul]
  rw [sum_comm]
  symm
  rw [sum_filter]
  apply sum_congr rfl
  intro a _
  by_cases ha : a.primeFactors ⊆ q.primeFactors
  · rw [ite_eq_left ha]
    simp only [mul_sum, ← mul_assoc, smoothDilationTerm_as_dilation q a f ha]
  · rw [ite_eq_right ha]
    symm
    apply sum_eq_zero
    intro m _
    rw [smoothDilationTerm, ite_eq_right (fun h => ha h.1), zero_mul]

/-- Finite short-window majorant: one genuine shorter window for each
smooth divisor, and one density term for all discarded smooth divisors. -/
theorem smooth_dilation_window_sum {f : ℕ → ℂ} (hf : Multiplicative f)
    (hfb : OneBounded f) (q K D Y : ℕ) (hq : 0 < q) (hK : 0 < K) (α : ℝ) :
    (∑ v ∈ range Y, ‖shortWindowSum (fun n => f (q * n)) D α v‖) ≤
      (∑ a ∈ (Icc 1 K).filter (fun a => a.primeFactors ⊆ q.primeFactors),
        ((a : ℝ) * (∑ m ∈ range (Y / a + 1),
          ‖shortWindowSum (coprimeRestriction q f) (D / a + 1) (a * α) m‖) + Y)) +
      (D : ℝ) * (Y + D) * (K : ℝ) ^ (-(1 / 2) : ℝ) *
        smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ) := by
  let A := (Icc 1 K).filter (fun a => a.primeFactors ⊆ q.primeFactors)
  have hs : (∑ v ∈ range Y, ‖shortWindowSum (truncatedDilation q f K) D α v‖) ≤
      ∑ a ∈ A, ((a : ℝ) * (∑ m ∈ range (Y / a + 1),
        ‖shortWindowSum (coprimeRestriction q f) (D / a + 1) (a * α) m‖) + Y) := by
    calc
      _ ≤ ∑ v ∈ range Y, ∑ a ∈ A,
          ‖shortWindowSum (dilationSequence a (coprimeRestriction q f)) D α v‖ := by
        apply sum_le_sum
        intro v _
        rw [truncated_shortWindowSum hf q K D v hq α]
        apply (norm_sum_le _ _).trans
        apply sum_le_sum
        intro a ha
        have hap : 0 < a := (mem_Icc.mp (mem_filter.mp ha).1).1
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hfb _ (Nat.mul_pos hq hap))
      _ = ∑ a ∈ A, ∑ v ∈ range Y,
          ‖shortWindowSum (dilationSequence a (coprimeRestriction q f)) D α v‖ := sum_comm
      _ ≤ _ := by
        apply sum_le_sum
        intro a ha
        have hap : 0 < a := (mem_Icc.mp (mem_filter.mp ha).1).1
        calc
          _ ≤ ∑ v ∈ range Y,
              (‖shortWindowSum (coprimeRestriction q f) (D / a + 1) (a * α) (v / a)‖ + 1) := by
            apply sum_le_sum
            intro v _
            rw [← norm_shortExponentialSum_eq_window]
            exact norm_shortExponentialSum_dilation_le _
              (coprimeRestriction_oneBounded q hfb) a D v hap α
          _ = (∑ v ∈ range Y,
              ‖shortWindowSum (coprimeRestriction q f) (D / a + 1) (a * α) (v / a)‖) + Y := by
            simp only [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, mul_one]
          _ ≤ _ := add_le_add
            (quotient_sample_sum_le _ (fun _ => norm_nonneg _) a Y hap) le_rfl
  calc
    _ ≤ (∑ v ∈ range Y, ‖shortWindowSum (truncatedDilation q f K) D α v‖) +
        ∑ v ∈ range Y, ‖shortWindowSum (fun n => f (q * n)) D α v -
          shortWindowSum (truncatedDilation q f K) D α v‖ := by
      rw [← sum_add_distrib]
      apply sum_le_sum
      intro v _
      have he : shortWindowSum (fun n => f (q * n)) D α v =
          shortWindowSum (truncatedDilation q f K) D α v +
          (shortWindowSum (fun n => f (q * n)) D α v -
            shortWindowSum (truncatedDilation q f K) D α v) := by abel
      calc
        _ = ‖shortWindowSum (truncatedDilation q f K) D α v +
            (shortWindowSum (fun n => f (q * n)) D α v -
              shortWindowSum (truncatedDilation q f K) D α v)‖ := congrArg norm he
        _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add hs (truncated_window_error hfb q K D Y hq hK α)

end TwoPointCorrelations

end OAI
