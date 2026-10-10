import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticEnergyDyadic
import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticEnergyEuler

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators Topology
open Filter

theorem dyadic_log_cutoff_bounds {a B : ℕ} (ha : 0 < a) (hB : 0 < B) :
    B < 2^(Nat.log 2 B+1)*a ∧ 2^(Nat.log 2 B+1)*a ≤ 2*B*a := by
  have hlow := Nat.lt_pow_succ_log_self (by decide : 1 < 2) B
  have hmul : 2^(Nat.log 2 B+1) ≤ 2^(Nat.log 2 B+1)*a := by
    simpa using Nat.mul_le_mul_left (2^(Nat.log 2 B+1)) ha
  refine ⟨hlow.trans_le hmul, ?_⟩
  have hpow := Nat.pow_log_le_self 2 hB.ne'
  rw [pow_succ]
  nlinarith

theorem positiveDivisorArray_large_energy_scalar_eventually :
    ∀ᶠ T : ℝ in atTop, ∀ (L B N q : ℕ), Squarefree L → 2 ≤ L →
      B < 2^N*L^4 → (2^N*L^4 : ℕ) ≤ Real.exp (T^2) →
      ∀ (u K lam z : ℝ), 1 < u → u ≤ T^((1 : ℝ)/100000) → T^((3 : ℝ)/4) ≤ K →
      0 ≤ lam → 0 < z → (∀ p ∈ L.primeFactors, z ≤ (p : ℝ)) →
      ∀ (A : ∀ p : ℕ, Finset (ZMod p)) (mInv : ℕ → ℤ) (R h θ : ℝ), 0 < R →
      (∑ s ∈ (Finset.Icc (L^4) B).filter (fun s => Squarefree s ∧ s.Coprime L),
        u^s.primeFactors.card * ‖positiveDivisorArray L q lam A mInv 1 R h θ s‖^2) ≤
      (N : ℝ) * Real.exp (2*(L.primeFactors.card : ℝ)/Real.sqrt z) *
        (Real.exp (K/200) * (quadraticCorrelationConstant *
          Real.exp ((L.primeFactors.card : ℝ)*(lam^2+2*lam/Real.sqrt z))) +
        cutoffFourierBound^2 * Real.exp (-10*K) * (1+lam)^(2*L.primeFactors.card)) := by
  filter_upwards [positiveDivisorArray_large_energy_eventually] with T hT
  intro L B N q hL hL2 hBN hNup u K lam z hu huup hK hlam hz hprimes A mInv R h θ hR
  apply (hT L B N q hL hL2 hBN hNup u K hu huup hK lam hlam A mInv R h θ hR).trans
  have hV : (reciprocalSqrtDivisorSum L)^2 ≤ Real.exp (2*(L.primeFactors.card : ℝ)/Real.sqrt z) := by
    calc
      _ ≤ (Real.exp ((L.primeFactors.card : ℝ)/Real.sqrt z))^2 :=
        pow_le_pow_left₀ (reciprocalSqrtDivisorSum_nonneg L)
          (reciprocalSqrtDivisorSum_le_exp hL hz hprimes) 2
      _ = _ := by rw [pow_two, ← Real.exp_add]; congr 1; ring
  have hEuler := quadratic_gram_euler_le_exp hlam hz hprimes
  have hC := quadraticCorrelationConstant_pos.le
  have hEuler0 : 0 ≤ ∏ p ∈ L.primeFactors, (1+lam^2+2*lam/Real.sqrt (p : ℝ)) := by
    exact Finset.prod_nonneg (fun p hp => by positivity)
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left hV (Nat.cast_nonneg N)
  · exact add_le_add
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hEuler hC) (Real.exp_pos _).le) le_rfl
  · positivity
  · positivity

theorem positiveDivisorArray_large_energy_log_eventually :
    ∀ᶠ T : ℝ in atTop, ∀ (L B q : ℕ), Squarefree L → 2 ≤ L → 0 < B →
      (2*B*L^4 : ℕ) ≤ Real.exp (T^2) →
      ∀ (u K lam z : ℝ), 1 < u → u ≤ T^((1 : ℝ)/100000) → T^((3 : ℝ)/4) ≤ K →
      0 ≤ lam → 0 < z → (∀ p ∈ L.primeFactors, z ≤ (p : ℝ)) →
      ∀ (A : ∀ p : ℕ, Finset (ZMod p)) (mInv : ℕ → ℤ) (R h θ : ℝ), 0 < R →
      (∑ s ∈ (Finset.Icc (L^4) B).filter (fun s => Squarefree s ∧ s.Coprime L),
        u^s.primeFactors.card * ‖positiveDivisorArray L q lam A mInv 1 R h θ s‖^2) ≤
      ((Nat.log 2 B+1 : ℕ) : ℝ) * Real.exp (2*(L.primeFactors.card : ℝ)/Real.sqrt z) *
        (Real.exp (K/200) * (quadraticCorrelationConstant *
          Real.exp ((L.primeFactors.card : ℝ)*(lam^2+2*lam/Real.sqrt z))) +
        cutoffFourierBound^2 * Real.exp (-10*K) * (1+lam)^(2*L.primeFactors.card)) := by
  filter_upwards [positiveDivisorArray_large_energy_scalar_eventually] with T hT
  intro L B q hL hL2 hB hBup u K lam z hu huup hK hlam hz hprimes A mInv R h θ hR
  have hcut := dyadic_log_cutoff_bounds (pow_pos (by omega : 0 < L) 4) hB
  apply hT L B (Nat.log 2 B+1) q hL hL2 hcut.1 _ u K lam z hu huup hK hlam hz hprimes A mInv R h θ hR
  exact (by exact_mod_cast hcut.2 : ((2^(Nat.log 2 B+1)*L^4 : ℕ) : ℝ) ≤ (2*B*L^4 : ℕ)).trans hBup

end Ostmann.QuadraticCenter

end

end OAI
