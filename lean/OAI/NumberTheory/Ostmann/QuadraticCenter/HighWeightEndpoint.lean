import OAI.NumberTheory.Ostmann.QuadraticCenter.HighWeightMass
import OAI.NumberTheory.Ostmann.QuadraticCenter.HighWeightRankin
import OAI.NumberTheory.Ostmann.Reuse.Mertens

namespace OAI

open Erdos970

namespace Ostmann.QuadraticCenter
open scoped BigOperators

def highWeightPrimeCutoff (X : ℕ) : Finset ℕ := (Finset.Ioc 0 (2 * X)).filter Nat.Prime

theorem highWeightPrimeCutoff_prime (X : ℕ) :
    ∀ p ∈ highWeightPrimeCutoff X, Nat.Prime p := by
  intro p hp
  exact (Finset.mem_filter.mp hp).2

theorem highWeightHalfDivisors_primeFactors {X L k r : ℕ}
    (hr : r ∈ highWeightHalfDivisors X L k) : r.primeFactors ⊆ highWeightPrimeCutoff X := by
  obtain ⟨hrX, hrs, hrc, hr2, hrω⟩ := mem_highWeightHalfDivisors.mp hr
  intro p hp
  obtain ⟨hpp, hpr, hr0⟩ := Nat.mem_primeFactors.mp hp
  exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr
    ⟨hpp.pos, (Nat.le_of_dvd (Nat.pos_of_ne_zero hr0) hpr).trans hrX⟩, hpp⟩

theorem high_weight_mass_le_rankin (S : Finset ℕ) {X L a k : ℕ}
    (hL : 0 < L) (hX : 2 * L ^ 2 ≤ X)
    (hS : ∀ n ∈ S, Squarefree n) (hcop : ∀ n ∈ S, n.Coprime L)
    (hres : ∀ n ∈ S, Nat.ModEq L n a)
    (hupper : ∀ n ∈ S, n ≤ 2 * X) (hweight : ∀ n ∈ S, 2 * k ≤ n.primeFactors.card)
    {u v : ℝ} (hu : 1 ≤ u) (hv : 1 ≤ v) :
    (∑ n ∈ S, u ^ n.primeFactors.card) ≤
      (3 * u * (X : ℝ) / (L : ℝ)) *
        (Real.exp (u ^ 2 * v * ∑ p ∈ highWeightPrimeCutoff X, 1 / (p : ℝ)) / v ^ k) := by
  have hu0 : 0 ≤ u := zero_le_one.trans hu
  apply (high_weight_mass_le_half_divisor_sum S hL hX hS hcop hres hupper hweight hu).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact squarefree_rankin_tail_le_exp (highWeightPrimeCutoff X) (highWeightHalfDivisors X L k)
    (highWeightPrimeCutoff_prime X)
    (fun r hr => (mem_highWeightHalfDivisors.mp hr).2.1)
    (fun r hr => highWeightHalfDivisors_primeFactors hr) k
    (fun r hr => (mem_highWeightHalfDivisors.mp hr).2.2.2.2) (sq_nonneg u) hv

theorem highWeightPrimeCutoff_reciprocal_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X →
      (∑ p ∈ highWeightPrimeCutoff X, 1 / (p : ℝ)) ≤
        Real.log (Real.log (2 * (X : ℝ))) + C := by
  obtain ⟨C, hC, hM⟩ := Ostmann.Reuse.primeReciprocal_abs_error_bound
  refine ⟨C, hC, ?_⟩
  intro X hX
  have hm := hM ((2 * X : ℕ) : ℝ) (by exact_mod_cast (show 2 ≤ 2 * X by omega))
  rw [Nat.floor_natCast] at hm
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hm
  have hu := (abs_le.mp hm).2
  change (∑ p ∈ highWeightPrimeCutoff X, 1 / (p : ℝ)) -
    Real.log (Real.log (2 * (X : ℝ))) ≤ C at hu
  linarith

theorem high_weight_mass_le_mertens :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset ℕ) (X L a k : ℕ),
      0 < L → 2 * L ^ 2 ≤ X →
      (∀ n ∈ S, Squarefree n) → (∀ n ∈ S, n.Coprime L) →
      (∀ n ∈ S, Nat.ModEq L n a) →
      (∀ n ∈ S, n ≤ 2 * X) → (∀ n ∈ S, 2 * k ≤ n.primeFactors.card) →
      ∀ u v : ℝ, 1 ≤ u → 1 ≤ v →
      (∑ n ∈ S, u ^ n.primeFactors.card) ≤
        (3 * u * (X : ℝ) / (L : ℝ)) *
          (Real.exp (u ^ 2 * v * (Real.log (Real.log (2 * (X : ℝ))) + C)) / v ^ k) := by
  obtain ⟨C, hC, hM⟩ := highWeightPrimeCutoff_reciprocal_upper
  refine ⟨C, hC, ?_⟩
  intro S X L a k hL hX hS hcop hres hupper hweight u v hu hv
  have hu0 : 0 ≤ u := zero_le_one.trans hu
  have hv0 : 0 ≤ v := zero_le_one.trans hv
  apply (high_weight_mass_le_rankin S hL hX hS hcop hres hupper hweight hu hv).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply hM X
  nlinarith

end Ostmann.QuadraticCenter

end OAI
