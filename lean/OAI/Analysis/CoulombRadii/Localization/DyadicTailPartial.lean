import Mathlib

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
namespace Coulomb

lemma dyadic_tail_partial_le {w : ℝ} (hw : 0 ≤ w) (N : ℕ) :
    (∑ k ∈ Finset.range N, if (4:ℝ)^k < w then (4:ℝ)^k else 0) ≤ (4/3:ℝ)*w := by
  induction N with
  | zero => simp only [Finset.range_zero, Finset.sum_empty]; positivity
  | succ N ih =>
    by_cases h : (4:ℝ)^N < w
    · calc
        _ ≤ ∑ k ∈ Finset.range (N+1), (4:ℝ)^k := by
          apply Finset.sum_le_sum
          intro k _
          split_ifs
          · exact le_rfl
          · positivity
        _ = ((4:ℝ)^(N+1)-1)/3 := by rw [geom_sum_eq (by norm_num : (4:ℝ) ≠ 1)]; norm_num
        _ ≤ (4/3:ℝ)*w := by rw [pow_succ]; linarith
    · simpa only [Finset.sum_range_succ, ite_eq_right h, add_zero] using ih

lemma dyadic_tail_hasSum {w : ℝ} (hw : 0 ≤ w) :
    Summable (fun k : ℕ => if (4:ℝ)^k < w then (4:ℝ)^k else 0) ∧
    (∑' k : ℕ, if (4:ℝ)^k < w then (4:ℝ)^k else 0) ≤ (4/3:ℝ)*w := by
  classical
  obtain ⟨N,hN⟩ := pow_unbounded_of_one_lt w (by norm_num : (1:ℝ) < 4)
  have hz (k : ℕ) (hk : k ∉ Finset.range N) :
      (if (4:ℝ)^k < w then (4:ℝ)^k else 0) = 0 := by
    have hNk : N ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
    have hpow : (4:ℝ)^N ≤ (4:ℝ)^k := pow_le_pow_right₀ (by norm_num) hNk
    exact ite_eq_right (not_lt.mpr (hN.le.trans hpow))
  refine ⟨summable_of_ne_finset_zero hz, ?_⟩
  rw [tsum_eq_sum hz]
  exact dyadic_tail_partial_le hw N

lemma pow_eight_two_thirds (k : ℕ) :
    ((8:ℝ)^k)^(2/3:ℝ) = (4:ℝ)^k := by
  rw [← Real.rpow_natCast_mul (by norm_num), mul_comm,
    Real.rpow_mul_natCast (by norm_num)]
  congr 1
  have he : (8:ℝ) = (2:ℝ)^(3:ℝ) := by norm_num
  rw [he, ← Real.rpow_mul (by norm_num)]
  norm_num

lemma dyadic_density_bound {B r : ℝ} (hB : 0 < B) (hr : 0 ≤ r)
    (h : ℕ → ℝ) (h0 : ∀ k, 0 ≤ h k)
    (hs : Summable (fun k => (4:ℝ)^k * h k))
    (hcap : ∀ k, r ≤ 2*B*(8:ℝ)^k + 2*h k) :
    r^(5/3:ℝ) ≤ (32*B)^(2/3:ℝ)*r +
      (4*(32*B)^(2/3:ℝ))*(∑' k, (4:ℝ)^k*h k) := by
  have hS : 0 ≤ ∑' k, (4:ℝ)^k*h k := tsum_nonneg (fun k => mul_nonneg (by positivity) (h0 k))
  have hfac : 0 ≤ (32*B)^(2/3:ℝ) := Real.rpow_nonneg (by positivity) _
  have hrpow : r^(5/3:ℝ) = r^(2/3:ℝ)*r := by
    by_cases hz : r = 0
    · simp [hz]
    · rw [show (5/3:ℝ) = 2/3+1 by norm_num, Real.rpow_add_one hz]
  by_cases hsmall : r ≤ 4*B
  · have hb : r^(2/3:ℝ) ≤ (32*B)^(2/3:ℝ) :=
      Real.rpow_le_rpow hr (hsmall.trans (by linarith)) (by norm_num)
    rw [hrpow]
    have ht := mul_le_mul_of_nonneg_right hb hr
    nlinarith [mul_nonneg hfac hS]
  · have hbig : 4*B < r := lt_of_not_ge hsmall
    obtain ⟨k,hk,hk'⟩ := exists_nat_pow_near
      ((le_div_iff₀ (by positivity : (0:ℝ) < 4*B)).2 (by linarith : 1*(4*B) ≤ r))
      (by norm_num : (1:ℝ) < 8)
    have hlo : 4*B*(8:ℝ)^k ≤ r := by
      have hh := (le_div_iff₀ (by positivity : (0:ℝ) < 4*B)).mp hk
      nlinarith
    have hup : r ≤ 32*B*(8:ℝ)^k := by
      have hh := (div_lt_iff₀ (by positivity : (0:ℝ) < 4*B)).mp hk'
      rw [pow_succ] at hh
      nlinarith
    have hh : r ≤ 4*h k := by have hc := hcap k; linarith
    have hpower : r^(2/3:ℝ) ≤ (32*B)^(2/3:ℝ)*(4:ℝ)^k := by
      have H := Real.rpow_le_rpow hr hup (by norm_num : (0:ℝ) ≤ 2/3)
      rwa [Real.mul_rpow (by positivity) (by positivity), pow_eight_two_thirds] at H
    have hsingle : (4:ℝ)^k*h k ≤ ∑' j, (4:ℝ)^j*h j :=
      hs.le_tsum k (fun j _ => mul_nonneg (by positivity) (h0 j))
    rw [hrpow]
    calc
      _ ≤ ((32*B)^(2/3:ℝ)*(4:ℝ)^k)*(4*h k) :=
        mul_le_mul hpower hh hr (by positivity)
      _ = (4*(32*B)^(2/3:ℝ))*((4:ℝ)^k*h k) := by ring
      _ ≤ (4*(32*B)^(2/3:ℝ))*(∑' j, (4:ℝ)^j*h j) :=
        mul_le_mul_of_nonneg_left hsingle (by positivity)
      _ ≤ _ := le_add_of_nonneg_left (mul_nonneg hfac hr)

lemma dyadic_spectral_tail_bound {α : Type*} (w c : α → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hc : ∀ a, 0 ≤ c a)
    (hs : Summable (fun a => w a*c a)) :
    Summable (fun k : ℕ => (4:ℝ)^k * (∑' a, if (4:ℝ)^k < w a then c a else 0)) ∧
    (∑' k : ℕ, (4:ℝ)^k * (∑' a, if (4:ℝ)^k < w a then c a else 0)) ≤
      (4/3:ℝ)*(∑' a, w a*c a) := by
  classical
  let F (a : α) (k : ℕ) := (if (4:ℝ)^k < w a then (4:ℝ)^k else 0)*c a
  have hF0 (a : α) (k : ℕ) : 0 ≤ F a k := by
    dsimp only [F]
    apply mul_nonneg _ (hc a)
    split_ifs <;> positivity
  have hFa (a : α) : Summable (F a) :=
    (dyadic_tail_hasSum (hw a)).1.mul_right (c a)
  have hFb (a : α) : (∑' k, F a k) ≤ (4/3:ℝ)*(w a*c a) := by
    rw [show (∑' k, F a k) = (∑' k, if (4:ℝ)^k < w a then (4:ℝ)^k else 0)*c a from
      tsum_mul_right]
    have H := mul_le_mul_of_nonneg_right (dyadic_tail_hasSum (hw a)).2 (hc a)
    simpa only [mul_assoc] using H
  have houter : Summable (fun a => ∑' k, F a k) :=
    Summable.of_nonneg_of_le (fun a => tsum_nonneg (hF0 a)) hFb (hs.mul_left (4/3:ℝ))
  have hprod : Summable (Function.uncurry F) :=
    (summable_prod_of_nonneg (fun z => hF0 z.1 z.2)).2 ⟨hFa,houter⟩
  have heq (k : ℕ) : (∑' a, F a k) =
      (4:ℝ)^k*(∑' a, if (4:ℝ)^k < w a then c a else 0) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro a
    dsimp only [F]
    split_ifs <;> simp only [zero_mul, mul_zero]
  refine ⟨?_, ?_⟩
  · simpa only [Prod.swap_prod_mk, Function.uncurry_apply_pair, heq] using hprod.prod_symm.prod
  · simp_rw [← heq]
    rw [hprod.tsum_comm]
    have H := houter.tsum_le_tsum hFb (hs.mul_left (4/3:ℝ))
    simpa only [tsum_mul_left] using H

end Coulomb

end
end

end OAI
