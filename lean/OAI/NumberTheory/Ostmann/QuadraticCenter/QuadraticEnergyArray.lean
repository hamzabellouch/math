import OAI.NumberTheory.Ostmann.QuadraticCenter.PositiveFrequencyDivisor
import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticEnergyLarge

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators Topology
open Filter

theorem weighted_complex_sum_sq_le {ι : Type*} (V : Finset ι)
    (w : ι → ℝ) (c z : ι → ℂ) (hw : ∀ v ∈ V, 0 ≤ w v)
    (hc : ∀ v ∈ V, ‖c v‖ ≤ w v) :
    ‖∑ v ∈ V, c v*z v‖^2 ≤ (∑ v ∈ V, w v) * ∑ v ∈ V, w v*‖z v‖^2 := by
  have hnorm : ‖∑ v ∈ V, c v*z v‖ ≤ ∑ v ∈ V, w v*‖z v‖ := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro v hv
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hc v hv) (norm_nonneg _)
  apply (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul V hw
    (fun v hv => mul_nonneg (hw v hv) (sq_nonneg _))
  intro v hv
  exact le_of_eq (by ring)

theorem positiveDivisorArray_one_eq_combination (L q : ℕ) (lam : ℝ)
    (A : ∀ p : ℕ, Finset (ZMod p)) (mInv : ℕ → ℤ)
    (s : ℕ) (R h θ : ℝ) :
    positiveDivisorArray L q lam A mInv 1 R h θ s =
      (Real.sqrt (s : ℝ) : ℂ)⁻¹ * ∑ v ∈ L.divisors,
        (jacobiSym (v : ℤ) q : ℂ)/(Real.sqrt (v : ℝ) : ℂ) *
          divisorQuadraticCombination L lam (fun d => (jacobiSym (d : ℤ) q : ℂ))
            A mInv s v R h θ := by
  simp only [positiveDivisorArray, divisorQuadraticSumP_one, divisorQuadraticCombination]

def reciprocalSqrtDivisorSum (L : ℕ) : ℝ := ∑ v ∈ L.divisors, (Real.sqrt (v : ℝ))⁻¹

theorem reciprocalSqrtDivisorSum_nonneg (L : ℕ) : 0 ≤ reciprocalSqrtDivisorSum L := by
  unfold reciprocalSqrtDivisorSum
  exact Finset.sum_nonneg (fun _ _ => by positivity)

theorem positiveDivisorArray_one_weighted_sq_le (L q s : ℕ) (lam : ℝ)
    (A : ∀ p : ℕ, Finset (ZMod p)) (mInv : ℕ → ℤ)
    (R h θ : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    u^s.primeFactors.card * ‖positiveDivisorArray L q lam A mInv 1 R h θ s‖^2 ≤
      reciprocalSqrtDivisorSum L * ∑ v ∈ L.divisors,
        (Real.sqrt (v : ℝ))⁻¹ * ((u^s.primeFactors.card / (s : ℝ)) *
          ‖divisorQuadraticCombination L lam (fun d => (jacobiSym (d : ℤ) q : ℂ))
            A mInv s v R h θ‖^2) := by
  have hJ (v : ℕ) : ‖(jacobiSym (v : ℤ) q : ℂ)‖ ≤ 1 := by
    rcases jacobiSym.trichotomy (v : ℤ) q with h | h | h <;> simp [h]
  have hc (v : ℕ) (hv : v ∈ L.divisors) :
      ‖(jacobiSym (v : ℤ) q : ℂ)/(Real.sqrt (v : ℝ) : ℂ)‖ ≤ (Real.sqrt (v : ℝ))⁻¹ := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    simpa only [one_div] using (div_le_div_of_nonneg_right (hJ v) (Real.sqrt_nonneg (v : ℝ)))
  have hh := weighted_complex_sum_sq_le L.divisors (fun v => (Real.sqrt (v : ℝ))⁻¹)
    (fun v => (jacobiSym (v : ℤ) q : ℂ)/(Real.sqrt (v : ℝ) : ℂ))
    (fun v => divisorQuadraticCombination L lam (fun d => (jacobiSym (d : ℤ) q : ℂ))
      A mInv s v R h θ) (fun _ _ => by positivity) hc
  rw [positiveDivisorArray_one_eq_combination, norm_mul, mul_pow, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg s)]
  calc
    _ = (u^s.primeFactors.card/(s : ℝ)) * ‖∑ v ∈ L.divisors,
        (jacobiSym (v : ℤ) q : ℂ)/(Real.sqrt (v : ℝ) : ℂ) *
          divisorQuadraticCombination L lam (fun d => (jacobiSym (d : ℤ) q : ℂ))
            A mInv s v R h θ‖^2 := by ring
    _ ≤ (u^s.primeFactors.card/(s : ℝ)) * ((∑ v ∈ L.divisors, (Real.sqrt (v : ℝ))⁻¹) *
        ∑ v ∈ L.divisors, (Real.sqrt (v : ℝ))⁻¹ *
          ‖divisorQuadraticCombination L lam (fun d => (jacobiSym (d : ℤ) q : ℂ))
            A mInv s v R h θ‖^2) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by
      simp only [reciprocalSqrtDivisorSum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      ring

theorem positiveDivisorArray_dyadic_energy_eventually :
    ∀ᶠ T : ℝ in atTop, ∀ (L S q : ℕ), Squarefree L → 2 ≤ L → L^4 ≤ S →
      ∀ (u K : ℝ), (S : ℝ) ≤ Real.exp (T^2) →
      1 < u → u ≤ T^((1 : ℝ)/100000) → T^((3 : ℝ)/4) ≤ K →
      ∀ (lam : ℝ), 0 ≤ lam →
      ∀ (A : ∀ p : ℕ, Finset (ZMod p)) (mInv : ℕ → ℤ) (R h θ : ℝ), 0 < R →
      (∑ s ∈ (Finset.Ico S (2*S)).filter (fun s => Squarefree s ∧ s.Coprime L),
        u^s.primeFactors.card * ‖positiveDivisorArray L q lam A mInv 1 R h θ s‖^2) ≤
      (reciprocalSqrtDivisorSum L)^2 *
        (Real.exp (K/200) * (quadraticCorrelationConstant *
          ∏ p ∈ L.primeFactors, (1+lam^2+2*lam/Real.sqrt (p : ℝ))) +
        cutoffFourierBound^2 * Real.exp (-10*K) * (1+lam)^(2*L.primeFactors.card)) := by
  filter_upwards [divisorQuadraticCombination_large_energy_eventually] with T hT
  intro L S q hL hL2 hS u K hSup hu huup hK lam hlam A mInv R h θ hR
  let I := (Finset.Ico S (2*S)).filter (fun s => Squarefree s ∧ s.Coprime L)
  let E := Real.exp (K/200) * (quadraticCorrelationConstant *
      ∏ p ∈ L.primeFactors, (1+lam^2+2*lam/Real.sqrt (p : ℝ))) +
      cutoffFourierBound^2 * Real.exp (-10*K) * (1+lam)^(2*L.primeFactors.card)
  have hη (d : ℕ) (hd : d ∈ L.divisors) : ‖(jacobiSym (d : ℤ) q : ℂ)‖ ≤ 1 := by
    rcases jacobiSym.trichotomy (d : ℤ) q with h | h | h <;> simp [h]
  calc
    _ ≤ ∑ s ∈ I, reciprocalSqrtDivisorSum L * ∑ v ∈ L.divisors,
        (Real.sqrt (v : ℝ))⁻¹ * ((u^s.primeFactors.card/(s : ℝ)) *
          ‖divisorQuadraticCombination L lam (fun d => (jacobiSym (d : ℤ) q : ℂ))
            A mInv s v R h θ‖^2) := by
      exact Finset.sum_le_sum (fun s hs =>
        positiveDivisorArray_one_weighted_sq_le L q s lam A mInv R h θ (by linarith))
    _ = reciprocalSqrtDivisorSum L * ∑ v ∈ L.divisors, (Real.sqrt (v : ℝ))⁻¹ *
        ∑ s ∈ I, (u^s.primeFactors.card/(s : ℝ)) *
          ‖divisorQuadraticCombination L lam (fun d => (jacobiSym (d : ℤ) q : ℂ))
            A mInv s v R h θ‖^2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ reciprocalSqrtDivisorSum L * ∑ v ∈ L.divisors, (Real.sqrt (v : ℝ))⁻¹ * E := by
      apply mul_le_mul_of_nonneg_left _ (reciprocalSqrtDivisorSum_nonneg L)
      apply Finset.sum_le_sum
      intro v hv
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hT L S v hL hL2 hS (Nat.pos_of_mem_divisors hv) u K hSup hu huup hK lam hlam
        (fun d => (jacobiSym (d : ℤ) q : ℂ)) hη A mInv R h θ hR
    _ = _ := by
      rw [← Finset.sum_mul]
      change _ = (reciprocalSqrtDivisorSum L)^2*E
      unfold reciprocalSqrtDivisorSum
      ring

end Ostmann.QuadraticCenter

end

end OAI
