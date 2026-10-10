import OAI.NumberTheory.TotientAsymptotic.PrimeBandProducts
import OAI.NumberTheory.TotientAsymptotic.NormalPrimeBands

namespace OAI

/-! Normality gives the factor-count caps required by the collision allocation bound. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma omegaIn_upper_truncate (n : ℕ) (U V : ℝ) :
    omegaIn n U V=omegaIn n U (min V n) := by
  unfold omegaIn
  congr 1
  apply List.filter_congr
  intro p hp
  have hpn : (p:ℝ) ≤ n := by exact_mod_cast Nat.le_of_mem_primeFactorsList hp
  simp only [le_min_iff,hpn,and_true]

lemma normality_band_upper {S U V : ℝ} {p : ℕ} (hp : IsNormalPrime S p)
    (hS : 1 < S) (hBS : 0 ≤ B S) (hSU : S ≤ U) (hUV : U < V) :
    (omegaIn (p-1) U V:ℝ) ≤ B V-B U+Real.sqrt (B S*B V) := by
  have hU1 : 1 < U := hS.trans_le hSU
  have hV1 : 1 < V := hU1.trans hUV
  have hBUV : B U ≤ B V :=
    Real.log_le_log (Real.log_pos hU1) (Real.log_le_log (by linarith) hUV.le)
  by_cases hn : (p-1:ℕ) ≤ U
  · have hp1 : 1 ≤ p-1 := by have := hp.1.two_le; omega
    have hlarge : (largestPrimeFactor (p-1):ℝ) ≤ U :=
      (show (largestPrimeFactor (p-1):ℝ) ≤ (p-1:ℕ) by
        exact_mod_cast largestPrimeFactor_le_self hp1).trans hn
    rw [omegaIn_eq_zero_of_largest_le hlarge,Nat.cast_zero]
    linarith [Real.sqrt_nonneg (B S*B V)]
  · have hn : U < (p-1:ℕ) := lt_of_not_ge hn
    let W := min V (p-1:ℕ)
    have hUW : U < W := lt_min hUV hn
    have hBW : B W ≤ B V := Real.log_le_log (Real.log_pos (hU1.trans hUW))
      (Real.log_le_log (by linarith) (min_le_left V (p-1:ℕ)))
    have hroot : Real.sqrt (B S*B W) ≤ Real.sqrt (B S*B V) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hBW hBS)
    have hb := (normality_interval_bounds hp hSU hUW (min_le_right V (p-1:ℕ)) hroot).2
    rw [omegaIn_upper_truncate]
    change (omegaIn (p-1) U W:ℝ) ≤ _
    linarith

lemma normal_band_product_omega {k : ℕ} (p : Fin k → ℕ) {S U V : ℝ}
    (hp : ∀ j,IsNormalPrime S (p j)) (hS : 1 < S) (hBS : 0 ≤ B S)
    (hSU : S ≤ U) (hUV : U < V) :
    ((∏ j,partBetween (p j-1) U V).primeFactorsList.length:ℝ) ≤
      (k:ℝ)*(B V-B U+Real.sqrt (B S*B V)) := by
  have hn (j : Fin k) : p j-1 ≠ 0 := by have := (hp j).1.two_le; omega
  rw [← partBetween_prod _ _ (fun j _ => hn j),partBetween_omega,
    omegaIn_prod _ _ (fun j _ => hn j),Nat.cast_sum]
  calc
    _ ≤ ∑ _j : Fin k,(B V-B U+Real.sqrt (B S*B V)) :=
      Finset.sum_le_sum (fun j _ => normality_band_upper (hp j) hS hBS hSU hUV)
    _ = _ := by simp; ring

end TotientAsymptotic

end

end OAI
