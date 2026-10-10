import OAI.NumberTheory.TwoPoint.Bounds.TruncatedDilation
import OAI.NumberTheory.TwoPoint.Bounds.WindowPolynomialBounds

namespace OAI

/-! Exact short-window reindexing for a sequence supported on multiples
of a fixed integer. Only one endpoint term is lost to a fixed window length. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def dilationSequence (a : ℕ) (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  if a ∣ n then f (n / a) else 0

lemma additiveCharacter_nat_mul (α : ℝ) (a m : ℕ) :
    additiveCharacter α (a * m) = additiveCharacter (a * α) m := by
  unfold additiveCharacter
  congr 1
  push_cast
  ring

lemma shortExponentialSum_dilation (f : ℕ → ℂ) (a D v : ℕ)
    (ha : 0 < a) (α : ℝ) :
    shortExponentialSum (dilationSequence a f) D α v =
      shortExponentialSum f ((v + D) / a - v / a) (a * α) ((v / a : ℕ) : ℝ) := by
  have hle : v / a ≤ (v + D) / a := Nat.div_le_div_right (Nat.le_add_right _ _)
  rw [shortExponentialSum_at_nat, shortExponentialSum_at_nat,
    Nat.add_sub_of_le hle]
  have hleft : (∑ n ∈ Icc (v + 1) (v + D),
      dilationSequence a f n * additiveCharacter α n) =
      ∑ n ∈ (Icc (v + 1) (v + D)).filter (fun n => a ∣ n),
        f (n / a) * additiveCharacter α n := by
    rw [sum_filter]
    apply sum_congr rfl
    intro n _
    unfold dilationSequence
    split_ifs <;> simp
  rw [hleft]
  symm
  apply sum_bij (fun m _ => a * m)
  · intro m hm
    obtain ⟨hm0, hm1⟩ := mem_Icc.mp hm
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨?_, ?_⟩, dvd_mul_right a m⟩
    · have ht : v < a * m := by
        have hh := (Nat.div_lt_iff_lt_mul ha).mp (show v / a < m by omega)
        simpa only [Nat.mul_comm] using hh
      omega
    · have hh := (Nat.le_div_iff_mul_le ha).mp hm1
      simpa only [Nat.mul_comm] using hh
  · intro m _ n _ he
    exact Nat.eq_of_mul_eq_mul_left ha he
  · intro n hn
    obtain ⟨hnI, hd⟩ := mem_filter.mp hn
    obtain ⟨hn0, hn1⟩ := mem_Icc.mp hnI
    refine ⟨n / a, mem_Icc.mpr ⟨?_, Nat.div_le_div_right hn1⟩,
      Nat.mul_div_cancel' hd⟩
    have he : v < a * (n / a) := by rw [Nat.mul_div_cancel' hd]; omega
    have hh : v / a < n / a := (Nat.div_lt_iff_lt_mul ha).mpr (by
      simpa only [Nat.mul_comm] using he)
    omega
  · intro m _
    rw [Nat.mul_div_cancel_left _ ha, additiveCharacter_nat_mul]

lemma quotient_window_length (a D v : ℕ) (_ha : 0 < a) :
    (v + D) / a - v / a = D / a ∨ (v + D) / a - v / a = D / a + 1 := by
  have hlo : v / a + D / a ≤ (v + D) / a := Nat.div_add_div_le_add_div
  have hhi := Nat.add_div_le_div_add_div_add_one v D a
  generalize (v + D) / a = t at *
  generalize v / a = u at *
  generalize D / a = w at *
  omega

lemma norm_shortWindowSum_le_succ (f : ℕ → ℂ) (hf : OneBounded f)
    (D v : ℕ) (α : ℝ) :
    ‖shortWindowSum f D α v‖ ≤ ‖shortWindowSum f (D + 1) α v‖ + 1 := by
  have he : shortWindowSum f (D + 1) α v = shortWindowSum f D α v +
      f (v + D + 1) * additiveCharacter α (D + 1) := by
    simp only [shortWindowSum, sum_range_succ]
  have hn : ‖f (v + D + 1) * additiveCharacter α (D + 1)‖ ≤ 1 := by
    rw [norm_mul, norm_additiveCharacter, mul_one]
    exact hf _ (by omega)
  have ht := norm_sub_le (shortWindowSum f (D + 1) α v)
    (f (v + D + 1) * additiveCharacter α (D + 1))
  have ht' : ‖shortWindowSum f D α v‖ ≤
      ‖shortWindowSum f (D + 1) α v‖ +
        ‖f (v + D + 1) * additiveCharacter α (D + 1)‖ := by
    simpa only [he, add_sub_cancel_right] using ht
  linarith

lemma norm_shortExponentialSum_dilation_le (f : ℕ → ℂ) (hf : OneBounded f)
    (a D v : ℕ) (ha : 0 < a) (α : ℝ) :
    ‖shortExponentialSum (dilationSequence a f) D α v‖ ≤
      ‖shortWindowSum f (D / a + 1) (a * α) (v / a)‖ + 1 := by
  rw [shortExponentialSum_dilation f a D v ha α,
    norm_shortExponentialSum_eq_window]
  rcases quotient_window_length a D v ha with he | he
  · rw [he]
    exact norm_shortWindowSum_le_succ f hf _ _ _
  · rw [he]
    exact le_add_of_nonneg_right zero_le_one

lemma quotient_sample_sum_le (F : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n)
    (a Y : ℕ) (ha : 0 < a) :
    (∑ v ∈ range Y, F (v / a)) ≤
      (a : ℝ) * ∑ m ∈ range (Y / a + 1), F m := by
  have hb : (∑ v ∈ range Y, F (v / a)) ≤
      ∑ x ∈ range (Y / a + 1) ×ˢ range a, F x.1 := by
    apply sum_le_sum_of_injOn (fun v => (v / a, v % a))
    · intro v _ w _ he
      have h1 := congrArg Prod.fst he
      have h2 := congrArg Prod.snd he
      nlinarith [Nat.div_add_mod v a, Nat.div_add_mod w a]
    · intro x hx
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hx
      exact mem_product.mpr ⟨mem_range.mpr (by
        have hh : v / a ≤ Y / a := Nat.div_le_div_right (Nat.le_of_lt (mem_range.mp hv))
        exact Nat.lt_succ_of_le hh),
        mem_range.mpr (Nat.mod_lt _ ha)⟩
    · intro v _
      exact le_rfl
    · intro x _ _
      exact hF x.1
  apply hb.trans_eq
  rw [sum_product]
  simp only [sum_const, card_range, nsmul_eq_mul, ← mul_sum]

end TwoPointCorrelations

end OAI
