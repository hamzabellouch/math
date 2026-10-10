import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticEnergyDivisors
import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticEnergyExpansion
import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticEnergyScale

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators ComplexConjugate

def divisorQuadraticCombination (L : ℕ) (lam : ℝ) (η : ℕ → ℂ)
    (A : ∀ p : ℕ, Finset (ZMod p)) (mInv : ℕ → ℤ)
    (s v : ℕ) (R h θ : ℝ) : ℂ :=
  ∑ d ∈ L.divisors, ((lam : ℂ) ^ d.primeFactors.card * η d) *
    divisorQuadraticSum d A (mInv d) s v R h θ

theorem divisorQuadraticCombination_energy_le {L S v : ℕ}
    (hL : Squarefree L) (hS : L ^ 2 ≤ S) (hv : 0 < v)
    (lam : ℝ) (hlam : 0 ≤ lam) (η : ℕ → ℂ) (hη : ∀ d ∈ L.divisors, ‖η d‖ ≤ 1)
    (A : ∀ p : ℕ, Finset (ZMod p)) (mInv : ℕ → ℤ)
    {R : ℝ} (hR : 0 < R) (h θ : ℝ) :
    (∑ s ∈ Finset.Ico S (2*S), (s : ℝ)⁻¹ *
      ‖divisorQuadraticCombination L lam η A mInv s v R h θ‖ ^ 2) ≤
      quadraticCorrelationConstant *
        ∏ p ∈ L.primeFactors, (1 + lam ^ 2 + 2 * lam / Real.sqrt (p : ℝ)) := by
  classical
  have hLpos : 0 < L := Nat.pos_of_ne_zero hL.ne_zero
  have hSpos : 0 < S := (pow_pos hLpos 2).trans_le hS
  let a : ℕ → ℂ := fun d => (lam : ℂ) ^ d.primeFactors.card * η d
  let G : ℕ → ℕ → ℂ := fun d s => divisorQuadraticSum d A (mInv d) s v R h θ
  have ha (d : ℕ) (hd : d ∈ L.divisors) : ‖a d‖ ≤ lam ^ d.primeFactors.card := by
    dsimp [a]
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlam]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hη d hd) (pow_nonneg hlam _)
  have hcor (d : ℕ) (hd : d ∈ L.divisors) (e : ℕ) (he : e ∈ L.divisors) :
      ‖∑ s ∈ Finset.Ico S (2*S), G d s * conj (G e s) / (s : ℂ)‖ ≤
        quadraticCorrelationConstant *
          ((Nat.gcd d e : ℝ) / (Real.sqrt (d : ℝ) * Real.sqrt (e : ℝ))) :=
    divisorQuadraticSum_dyadic_correlation
      (hL.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd))
      (hL.squarefree_of_dvd (Nat.dvd_of_mem_divisors he)) A (mInv d) (mInv e)
      hSpos hv hR h θ (divisor_lcm_harmonic_le hLpos
        (Nat.dvd_of_mem_divisors hd) (Nat.dvd_of_mem_divisors he) hS)
  calc
    _ ≤ ∑ d ∈ L.divisors, ∑ e ∈ L.divisors, ‖a d‖ * ‖a e‖ *
        ‖∑ s ∈ Finset.Ico S (2*S), G d s * conj (G e s) / (s : ℂ)‖ :=
      weighted_complex_energy_le_correlations L.divisors (Finset.Ico S (2*S)) a G
    _ ≤ ∑ d ∈ L.divisors, ∑ e ∈ L.divisors,
        lam ^ d.primeFactors.card * lam ^ e.primeFactors.card *
          (quadraticCorrelationConstant *
            ((Nat.gcd d e : ℝ) / (Real.sqrt (d : ℝ) * Real.sqrt (e : ℝ)))) := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro e he
      apply mul_le_mul
      · exact mul_le_mul (ha d hd) (ha e he) (norm_nonneg _) (pow_nonneg hlam _)
      · exact hcor d hd e he
      · exact norm_nonneg _
      · exact mul_nonneg (pow_nonneg hlam _) (pow_nonneg hlam _)
    _ = _ := by
      rw [← squarefree_divisor_gram_euler_product hL lam]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      ring

theorem divisorQuadraticCombination_energy_le_of_fourth_power {L S v : ℕ}
    (hL : Squarefree L) (hS : L ^ 4 ≤ S) (hv : 0 < v)
    (lam : ℝ) (hlam : 0 ≤ lam) (η : ℕ → ℂ) (hη : ∀ d ∈ L.divisors, ‖η d‖ ≤ 1)
    (A : ∀ p : ℕ, Finset (ZMod p)) (mInv : ℕ → ℤ)
    {R : ℝ} (hR : 0 < R) (h θ : ℝ) :
    (∑ s ∈ Finset.Ico S (2*S), (s : ℝ)⁻¹ *
      ‖divisorQuadraticCombination L lam η A mInv s v R h θ‖ ^ 2) ≤
      quadraticCorrelationConstant *
        ∏ p ∈ L.primeFactors, (1 + lam ^ 2 + 2 * lam / Real.sqrt (p : ℝ)) := by
  apply divisorQuadraticCombination_energy_le hL _ hv lam hlam η hη A mInv hR h θ
  have hL1 : 1 ≤ L := Nat.pos_of_ne_zero hL.ne_zero
  have hh : L ^ 2 ≤ L ^ 4 := pow_le_pow_right₀ hL1 (by decide)
  exact hh.trans hS

end Ostmann.QuadraticCenter

end

end OAI
