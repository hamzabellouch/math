import OAI.NumberTheory.Ostmann.QuadraticCenter.AdaptiveArrayDivisor
import OAI.NumberTheory.Ostmann.QuadraticCenter.PositiveFrequencyDivisorExpansion

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem normalizedSmoothQuadraticSum_eq_zero_of_scale_lt {P : ℕ} {N : ℝ}
    (hN : 0 ≤ N) (hP : N < P) (a : ℕ → ℂ) (α : ℝ) :
    normalizedSmoothQuadraticSum P N a α = 0 := by
  have hempty : cutoffMultiples P N = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    have hw' := Finset.mem_filter.mp hw
    have hwpos := (Finset.mem_Ioc.mp hw'.1).1
    have hPw : P ≤ w := Nat.le_of_dvd hwpos hw'.2
    have hwfloor : (w : ℝ) ≤ (⌊N⌋₊ : ℝ) := by
      exact_mod_cast (Finset.mem_Ioc.mp hw'.1).2
    have hwN : (w : ℝ) ≤ N := hwfloor.trans (Nat.floor_le hN)
    exact (not_lt_of_ge ((by exact_mod_cast hPw : (P : ℝ) ≤ w).trans hwN)) hP
  simp only [normalizedSmoothQuadraticSum, hempty, Finset.sum_empty, mul_zero]

theorem divisor_quadratic_scale_le {L d s v B : ℕ} (hd : 0 < d) (hdL : d ≤ L)
    (hs : 0 < s) (hv : 0 < v) {R : ℝ} (hR : 0 < R)
    (hB : R*L ≤ (B : ℝ)^2) : Real.sqrt (R/((s : ℝ)*v/d)) ≤ B := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  have hsv : (1 : ℝ) ≤ (s : ℝ)*v := by exact_mod_cast Nat.mul_pos hs hv
  have hdL' : (d : ℝ) ≤ L := by exact_mod_cast hdL
  have hquot : R/((s : ℝ)*v/d) = R*d/((s : ℝ)*v) := by field_simp
  apply (Real.sqrt_le_left (Nat.cast_nonneg B)).mpr
  rw [hquot]
  apply (div_le_iff₀ (mul_pos hs' hv')).mpr
  exact ((mul_le_mul_of_nonneg_left hdL' hR.le).trans hB).trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hsv (sq_nonneg (B : ℝ)))

theorem positiveDivisorArray_eq_zero_of_large_P {L s P B : ℕ} (hL : Squarefree L)
    (q : ℕ) (lam : ℝ) (A : ∀ p : ℕ, Finset (ZMod p)) (mInv : ℕ → ℤ)
    (hs : 0 < s) {R : ℝ} (hR : 0 < R) (h θ : ℝ)
    (hB : R*L ≤ (B : ℝ)^2) (hP : B < P) :
    positiveDivisorArray L q lam A mInv P R h θ s = 0 := by
  have hG (d : ℕ) (hd : d ∈ L.divisors) (v : ℕ) (hv : v ∈ L.divisors) :
      divisorQuadraticSumP d A (mInv d) s v P R h θ = 0 := by
    have hdsq := hL.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
    rw [divisorQuadraticSumP_eq_normalized hdsq]
    apply normalizedSmoothQuadraticSum_eq_zero_of_scale_lt (Real.sqrt_nonneg _)
    exact (divisor_quadratic_scale_le (Nat.pos_of_mem_divisors hd)
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hL.ne_zero) (Nat.dvd_of_mem_divisors hd))
      hs (Nat.pos_of_mem_divisors hv) hR hB).trans_lt (by exact_mod_cast hP)
  unfold positiveDivisorArray
  suffices hzero : (∑ v ∈ L.divisors, (jacobiSym (v : ℤ) q : ℂ)/(Real.sqrt (v : ℝ) : ℂ) *
      ∑ d ∈ L.divisors, (lam : ℂ)^d.primeFactors.card * (jacobiSym (d : ℤ) q : ℂ) *
        divisorQuadraticSumP d A (mInv d) s v P R h θ) = 0 by rw [hzero, mul_zero]
  apply Finset.sum_eq_zero
  intro v hv
  have hd0 : (∑ d ∈ L.divisors, (lam : ℂ)^d.primeFactors.card * (jacobiSym (d : ℤ) q : ℂ) *
      divisorQuadraticSumP d A (mInv d) s v P R h θ) = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    rw [hG d hd v hv, mul_zero]
  rw [hd0, mul_zero]

end Ostmann.QuadraticCenter

end

end OAI
