import OAI.NumberTheory.Jacobsthal.Estimates.FiniteSampleSpace

namespace OAI

namespace Erdos970

section

namespace ErdosInverseSampling
attribute [local instance] Classical.decEq

theorem sample_length_le (n h : ℕ) (beta : ℝ) (hb : 0 < beta) (hb1 : beta ≤ 1)
    (hsize : 4*(h : ℝ)/beta ≤ (n : ℝ)) : h ≤ n := by
  have hh := (div_le_iff₀ hb).mp hsize
  have hbmul := mul_le_mul_of_nonneg_right hb1 (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hr : (h : ℝ) ≤ n := by nlinarith [show (0 : ℝ) ≤ h from Nat.cast_nonneg h]
  exact_mod_cast hr

theorem falling_ratio_lower (n m h : ℕ) (beta : ℝ) (hb : 0 < beta) (hb1 : beta ≤ 1)
    (hgood : (beta/2)*(n : ℝ) ≤ (m : ℝ))
    (hsize : 4*(h : ℝ)/beta ≤ (n : ℝ)) :
    (beta/4)^h ≤ (m.descFactorial h : ℝ)/(n.descFactorial h : ℝ) := by
  have hhn := sample_length_le n h beta hb hb1 hsize
  have hpay := (div_le_iff₀ hb).mp hsize
  have hhm : h ≤ m := by
    have hh : (h : ℝ) ≤ m := by nlinarith [show (0 : ℝ) ≤ h from Nat.cast_nonneg h]
    exact_mod_cast hh
  have hnum : ((beta/4)*(n : ℝ))^h ≤ (m.descFactorial h : ℝ) := by
    rw [Nat.descFactorial_eq_prod_range,Nat.cast_prod]
    calc
      _ = ∏ _i ∈ Finset.range h,(beta/4)*(n : ℝ) := by simp
      _ ≤ ∏ i ∈ Finset.range h,((m-i : ℕ) : ℝ) := by
        apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
        intro i hi
        have hih : i < h := Finset.mem_range.mp hi
        have him : i ≤ m := by omega
        rw [Nat.cast_sub him]
        have hiR : (i : ℝ) ≤ h := by exact_mod_cast hih.le
        nlinarith
  have hden : (n.descFactorial h : ℝ) ≤ (n : ℝ)^h := by
    exact_mod_cast Nat.descFactorial_le_pow n h
  have hdenpos : (0 : ℝ) < n.descFactorial h := by exact_mod_cast Nat.descFactorial_pos.mpr hhn
  apply (le_div_iff₀ hdenpos).mpr
  calc
    _ ≤ (beta/4)^h*(n : ℝ)^h := mul_le_mul_of_nonneg_left hden (by positivity)
    _ = ((beta/4)*(n : ℝ))^h := by rw [mul_pow]
    _ ≤ _ := hnum

theorem sampleFrequency_lower {α : Type*} (U W : Finset α) (hWU : W ⊆ U) (h : ℕ)
    (beta : ℝ) (hb : 0 < beta) (hb1 : beta ≤ 1)
    (hgood : (beta/2)*(U.card : ℝ) ≤ (W.card : ℝ))
    (hsize : 4*(h : ℝ)/beta ≤ (U.card : ℝ)) :
    (beta/4)^h ≤ sampleFrequency U W h := by
  rw [sampleFrequency_eq U W hWU h]
  exact falling_ratio_lower U.card W.card h beta hb hb1 hgood hsize

theorem sample_nonempty_of_length {α : Type*} (U : Finset α) (h : ℕ) (hh : h ≤ U.card) :
    Nonempty (Sample U h) := by
  apply Fintype.card_pos_iff.mp
  rw [sample_card]
  exact Nat.descFactorial_pos.mpr hh

end ErdosInverseSampling

end

end Erdos970

end OAI
