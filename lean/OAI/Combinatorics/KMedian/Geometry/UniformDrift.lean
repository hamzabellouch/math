import Mathlib
import OAI.Combinatorics.KMedian.Process.AveragedDrift

namespace OAI

section
section
namespace MetricKMedian.GraphComparison
open Analytic

variable {I : Type*} [Fintype I]

theorem uniform_zero_drift {g y pHat : ℝ} {d N s : I → ℝ} {q K : I → I → ℝ}
    (hg : 0 < g) (hy : ∑ _i : I, g=y)
    (hd : ∀ i, 0 ≤ d i) (hV : ∑ i, g*d i=0)
    (hN : ∀ i, 0 ≤ N i) (hp : pHat ≤ 1/2)
    (hq0 : ∀ i t, 0 ≤ q i t) (hq : ∀ i t, q i t ≤ 1)
    (hcomp : ∀ i t, q i t < 1 → N i*(1-pHat*q i t) ≤ d i+d t) (x : ℝ) :
    unnormalizedDrift (fun _ => g) d N s q K x y pHat=0 := by
  have hd0 : ∀ i, d i=0 := by
    intro i
    have hterm := Finset.single_le_sum (s := Finset.univ)
      (fun t _ => mul_nonneg hg.le (hd t)) (Finset.mem_univ i)
    rw [hV] at hterm
    exact le_antisymm (by nlinarith only [hterm, hg]) (hd i)
  have hrad : ∀ i, (y-∑ t, g*q i t)*N i=0 := by
    intro i
    by_cases hNi : N i=0
    · rw [hNi, mul_zero]
    have hNp : 0 < N i := lt_of_le_of_ne (hN i) (Ne.symm hNi)
    have hrow : ∀ t, q i t=1 := by
      intro t
      apply le_antisymm (hq i t)
      by_contra hn
      have ht := hcomp i t (lt_of_not_ge hn)
      rw [hd0 i, hd0 t, add_zero] at ht
      have hprod := mul_le_mul hp (hq i t) (hq0 i t) (by norm_num : (0:ℝ) ≤ 1/2)
      have hden : 0 < 1-pHat*q i t := by nlinarith only [hprod]
      exact (not_lt_of_ge ht) (mul_pos hNp hden)
    simp only [hrow, mul_one, hy, sub_self, zero_mul]
  unfold unnormalizedDrift
  simp only [hd0, mul_zero, sub_zero, max_self, Finset.sum_const_zero,
    zero_mul, add_zero, zero_add]
  apply Finset.sum_eq_zero
  intro i _
  have hi := hrad i
  calc
    g*((y-∑ t, g*q i t)*((1-pHat*s i)*N i)) = g*(1-pHat*s i)*((y-∑ t, g*q i t)*N i) := by ring
    _ = 0 := by rw [hi, mul_zero]

theorem uniform_drift_le {g x y pHat ζ : ℝ} {d N s : I → ℝ} {q K : I → I → ℝ}
    (hg : 0 < g) (hx0 : 0 ≤ x) (hx : x ≤ 1)
    (hysum : ∑ _i : I, g=y) (hy : y ≤ 1)
    (hd : ∀ i, 0 ≤ d i) (hN : ∀ i, 0 ≤ N i)
    (hs0 : ∀ i, 0 ≤ s i) (hs : ∀ i, s i ≤ 1)
    (hq0 : ∀ i t, 0 ≤ q i t) (hq : ∀ i t, q i t ≤ 1)
    (hp0 : 0 ≤ pHat) (hp : pHat ≤ 1/2) (hζ0 : 0 ≤ ζ) (hζ : ζ < 1/4)
    (he : |pHat-Analytic.P x| ≤ ζ)
    (hcomp : ∀ i t, q i t < 1 → N i*(1-pHat*q i t) ≤ d i+d t)
    (hK : ∀ i t, K i t ≤
      (s i*(1-∑ u, g*q i u)+s t*(1-∑ u, g*q t u))/2) :
    unnormalizedDrift (fun _ => g) d N s q K x y pHat ≤ 12*ζ*(∑ i, g*d i) := by
  have hV0 : 0 ≤ ∑ i, g*d i := Finset.sum_nonneg (fun i _ => mul_nonneg hg.le (hd i))
  rcases eq_or_lt_of_le hV0 with hz | hV
  · rw [uniform_zero_drift hg hysum hd hz.symm hN hp hq0 hq hcomp x, ← hz, mul_zero]
  have hy0 : 0 < y := by
    by_contra hn
    have hzero : ∀ i : I, g=0 := by
      intro i
      have ht := Finset.single_le_sum (s := Finset.univ) (f := fun _ : I => g)
        (fun _ _ => hg.le) (Finset.mem_univ i)
      rw [hysum] at ht
      exact le_antisymm (ht.trans (le_of_not_gt hn)) hg.le
    have hz : ∑ i, g*d i=0 := Finset.sum_eq_zero (fun i _ => by rw [hzero i, zero_mul])
    exact (ne_of_gt hV) hz
  exact unnormalized_drift_le hx0 hx hy0 hy (fun _ => hg.le) hysum hd hV hN
    hs0 hs hq0 hq hp0 hp hζ0 hζ he hcomp hK

end MetricKMedian.GraphComparison
end
end

end OAI
