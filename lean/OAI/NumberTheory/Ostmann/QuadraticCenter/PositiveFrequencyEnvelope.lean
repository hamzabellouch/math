import OAI.NumberTheory.Ostmann.QuadraticCenter.AdaptiveArrayDivisor
import OAI.NumberTheory.Ostmann.QuadraticCenter.DivisorGram
import OAI.NumberTheory.Ostmann.QuadraticCenter.HighWeightRankin

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem positive_array_divisor_weight_sum {L : ℕ} (hL : Squarefree L) (lam : ℝ) :
    (∑ d ∈ L.divisors, lam ^ d.primeFactors.card) = (1 + lam) ^ L.primeFactors.card := by
  classical
  have hP : ∀ p ∈ L.primeFactors, p.Prime := fun p hp => (Nat.mem_primeFactors.mp hp).1
  rw [sum_squarefree_divisors_eq_cube hL]
  simp_rw [primeSubsetProduct_primeFactors_card hP]
  simpa only [one_pow, mul_one, Fintype.card_coe, add_comm] using
    Fintype.sum_pow_mul_eq_add_pow L.primeFactors lam (1 : ℝ)

def positiveArrayEnvelope (L : ℕ) (lam : ℝ) (P : ℕ) : ℝ :=
  (Real.sqrt (L : ℝ) * cutoffFourierBound / P) * (1+lam)^L.primeFactors.card *
    ∑ v ∈ L.divisors, (Real.sqrt (v : ℝ))⁻¹

theorem positiveArrayEnvelope_nonneg (L P : ℕ) {lam : ℝ} (hlam : 0 ≤ lam) :
    0 ≤ positiveArrayEnvelope L lam P := by
  unfold positiveArrayEnvelope
  exact mul_nonneg (mul_nonneg (div_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) cutoffFourierBound_pos.le) (Nat.cast_nonneg _))
    (pow_nonneg (by linarith) _)) (Finset.sum_nonneg (fun _ _ => by positivity))

private theorem envelope_jacobi_norm (n q : ℕ) : ‖(jacobiSym (n : ℤ) q : ℂ)‖ ≤ 1 := by
  rcases jacobiSym.trichotomy (n : ℤ) q with h | h | h <;> simp [h]

theorem positiveDivisorArray_norm_envelope {L s : ℕ} (hL : Squarefree L)
    (q : ℕ) {lam : ℝ} (hlam : 0 ≤ lam)
    (A : ∀ p : ℕ, Finset (ZMod p)) (mInv : ℕ → ℤ) (hs : 0 < s)
    (P : ℕ) {R : ℝ} (hR : 0 < R) (h θ : ℝ) :
    ‖positiveDivisorArray L q lam A mInv P R h θ s‖ ≤
      positiveArrayEnvelope L lam P / Real.sqrt (s : ℝ) := by
  classical
  let D : ℝ := Real.sqrt (L : ℝ) * cutoffFourierBound / P
  have hC : 0 ≤ cutoffFourierBound := cutoffFourierBound_pos.le
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hinner (v : ℕ) (hv : v ∈ L.divisors) :
      ‖∑ d ∈ L.divisors, (lam : ℂ)^d.primeFactors.card * (jacobiSym (d : ℤ) q : ℂ) *
        divisorQuadraticSumP d A (mInv d) s v P R h θ‖ ≤ D*(1+lam)^L.primeFactors.card := by
    calc
      _ ≤ ∑ d ∈ L.divisors,
        ‖(lam : ℂ)^d.primeFactors.card * (jacobiSym (d : ℤ) q : ℂ) *
          divisorQuadraticSumP d A (mInv d) s v P R h θ‖ := norm_sum_le _ _
      _ ≤ ∑ d ∈ L.divisors, lam^d.primeFactors.card * D := by
        apply Finset.sum_le_sum
        intro d hd
        have hdL : (d : ℝ) ≤ L := by
          exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hL.ne_zero) (Nat.dvd_of_mem_divisors hd)
        have hG := divisorQuadraticSumP_norm_le
          (hL.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)) A (mInv d) hs
          (Nat.pos_of_mem_divisors hv) P hR h θ
        have hGD : ‖divisorQuadraticSumP d A (mInv d) s v P R h θ‖ ≤ D :=
          hG.trans (div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hdL) cutoffFourierBound_pos.le)
            (Nat.cast_nonneg _))
        rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlam]
        calc
          _ ≤ (lam^d.primeFactors.card * 1) * D :=
            mul_le_mul (mul_le_mul_of_nonneg_left (envelope_jacobi_norm d q) (pow_nonneg hlam _))
              hGD (norm_nonneg _) (by positivity)
          _ = _ := by ring
      _ = _ := by rw [← Finset.sum_mul, positive_array_divisor_weight_sum hL]; ring
  have houter :
      ‖∑ v ∈ L.divisors, (jacobiSym (v : ℤ) q : ℂ)/(Real.sqrt (v : ℝ) : ℂ) *
        ∑ d ∈ L.divisors, (lam : ℂ)^d.primeFactors.card * (jacobiSym (d : ℤ) q : ℂ) *
          divisorQuadraticSumP d A (mInv d) s v P R h θ‖ ≤ positiveArrayEnvelope L lam P := by
    calc
      _ ≤ ∑ v ∈ L.divisors, ‖(jacobiSym (v : ℤ) q : ℂ)/(Real.sqrt (v : ℝ) : ℂ) *
        ∑ d ∈ L.divisors, (lam : ℂ)^d.primeFactors.card * (jacobiSym (d : ℤ) q : ℂ) *
          divisorQuadraticSumP d A (mInv d) s v P R h θ‖ := norm_sum_le _ _
      _ ≤ ∑ v ∈ L.divisors, (Real.sqrt (v : ℝ))⁻¹ * (D*(1+lam)^L.primeFactors.card) := by
        apply Finset.sum_le_sum
        intro v hv
        rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _)]
        have hvcoef : ‖(jacobiSym (v : ℤ) q : ℂ)‖ / Real.sqrt (v : ℝ) ≤
            (Real.sqrt (v : ℝ))⁻¹ := by
          simpa only [one_div] using
            (div_le_div_of_nonneg_right (envelope_jacobi_norm v q) (Real.sqrt_nonneg (v : ℝ)))
        exact mul_le_mul hvcoef (hinner v hv) (norm_nonneg _) (by positivity)
      _ = _ := by rw [← Finset.sum_mul]; unfold positiveArrayEnvelope; dsimp [D]; ring
  unfold positiveDivisorArray
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (mul_le_mul_of_nonneg_left houter (by positivity)).trans_eq (by ring)

end Ostmann.QuadraticCenter

end

end OAI
