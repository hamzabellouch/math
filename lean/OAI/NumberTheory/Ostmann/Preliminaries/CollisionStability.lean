import OAI.NumberTheory.Ostmann.Preliminaries.ActualMass
import OAI.NumberTheory.Ostmann.Preliminaries.CollisionIdentity
import OAI.NumberTheory.Ostmann.Preliminaries.PrimeSums

namespace OAI

open Erdos970

namespace Ostmann.Preliminaries
open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

noncomputable def localCollisionStability (d : Decomposition) (p : ℕ) [NeZero p]
    (a : α → ℕ) (μ : α → ℝ) (b : β → ℕ) (ν : β → ℝ) : ℝ :=
  uniformDefect (d.residueSupport p) (projectedMass (fun i => (a i : ZMod p)) μ) +
  uniformDefect (d.residueSupport p)ᶜ (projectedMass (fun i => -(b i : ZMod p)) ν) +
  ((d.residueDensity p)⁻¹ + (1 - d.residueDensity p)⁻¹ - 4) / p

noncomputable def collisionStability (d : Decomposition) (Q : ℕ)
    (a : α → ℕ) (μ : α → ℝ) (b : β → ℕ) (ν : β → ℝ) : ℝ :=
  ∑ p : PrimeUpTo Q, Real.log p.val * localCollisionStability d p.val a μ b ν

omit [DecidableEq α] [DecidableEq β] in
theorem localCollisionStability_nonneg (d : Decomposition) (p : ℕ) [NeZero p]
    (hp : p.Prime) (a : α → ℕ) (μ : α → ℝ) (b : β → ℕ) (ν : β → ℝ) :
    0 ≤ localCollisionStability d p a μ b ν := by
  obtain ⟨h1, h2, h3⟩ := collision_stability_terms_nonneg (d.residueSupport p)
    (d.residueSupport_nonempty p) (d.residueSupport_compl_nonempty p hp)
    (projectedMass (fun i => (a i : ZMod p)) μ)
    (projectedMass (fun i => -(b i : ZMod p)) ν)
  exact add_nonneg (add_nonneg h1 h2) h3

omit [DecidableEq α] [DecidableEq β] in
theorem collisionStability_eq (d : Decomposition) (Q : ℕ)
    (a : α → ℕ) (μ : α → ℝ) (b : β → ℕ) (ν : β → ℝ)
    (hμ : ∑ i, μ i = 1) (hν : ∑ i, ν i = 1)
    (hA : ∀ i, μ i ≠ 0 → a i ∈ d.A) (hB : ∀ i, ν i ≠ 0 → b i ∈ d.B)
    (ha : ∀ i, μ i ≠ 0 → Q + d.cutoff < a i)
    (hb : ∀ i, ν i ≠ 0 → Q + d.cutoff < b i) :
    collisionStability d Q a μ b ν =
      (∑ p ∈ Q.primesLE, Real.log p * congruenceCollisionEnergy p a μ) +
      (∑ p ∈ Q.primesLE, Real.log p * congruenceCollisionEnergy p b ν) -
      4 * ∑ p ∈ Q.primesLE, Real.log (p : ℝ) / p := by
  have hlocal (p : PrimeUpTo Q) : localCollisionStability d p.val a μ b ν =
      congruenceCollisionEnergy p.val a μ + congruenceCollisionEnergy p.val b ν - 4 / p.val := by
    have h := decomposition_collision_identity d p.val (primeUpTo_prime p)
      (projectedMass (fun i => (a i : ZMod p.val)) μ)
      (projectedMass (fun i => -(b i : ZMod p.val)) ν)
      (by simpa only [projectedMass_sum] using hμ)
      (by simpa only [projectedMass_sum] using hν)
      (projected_A_supported d p.val a μ hA (fun i hi => by have := primeUpTo_le p; have := ha i hi; omega))
      (projected_neg_B_supported d p.val (primeUpTo_prime p) b ν hB
        (fun i hi => by have := primeUpTo_le p; have := hb i hi; omega))
    simpa only [localCollisionStability, ← congruenceCollisionEnergy_eq_projected, neg_projectedMass_energy] using h
  unfold collisionStability
  simp_rw [hlocal, mul_sub, mul_add]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    sum_primeUpTo Q (fun p => Real.log p * congruenceCollisionEnergy p a μ),
    sum_primeUpTo Q (fun p => Real.log p * congruenceCollisionEnergy p b ν),
    sum_primeUpTo Q (fun p => Real.log p * (4 / (p : ℝ)))]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  ring

theorem collisionStability_le (d : Decomposition) (Q X : ℕ) (hQ : 1 ≤ Q) (hX : 1 ≤ X)
    (a : α → ℕ) (μ : α → ℝ) (b : β → ℕ) (ν : β → ℝ)
    (hai : Function.Injective a) (hbi : Function.Injective b)
    (haX : ∀ i, a i ≤ X) (hbX : ∀ i, b i ≤ X)
    (hμ0 : ∀ i, 0 ≤ μ i) (hν0 : ∀ i, 0 ≤ ν i)
    (hμ : ∑ i, μ i = 1) (hν : ∑ i, ν i = 1)
    (hA : ∀ i, μ i ≠ 0 → a i ∈ d.A) (hB : ∀ i, ν i ≠ 0 → b i ∈ d.B)
    (ha : ∀ i, μ i ≠ 0 → Q + d.cutoff < a i)
    (hb : ∀ i, ν i ≠ 0 → Q + d.cutoff < b i)
    {M : ℝ} (hμcap : ∀ i, μ i ≤ M) (hνcap : ∀ i, ν i ≤ M) :
    collisionStability d Q a μ b ν ≤
      2 * Real.log X - 4 * Real.log Q + 2 * Real.log 4 * Q * M + 4 * (Real.log 4 + 4) := by
  rw [collisionStability_eq d Q a μ b ν hμ hν hA hB ha hb]
  have hEa := weighted_prime_collision_energy_le Q X a μ hX hai haX hμ0 hμ hμcap
  have hEb := weighted_prime_collision_energy_le Q X b ν hX hbi hbX hν0 hν hνcap
  have hM := mertens_prime_sum_lower Q hQ
  linarith

end Ostmann.Preliminaries

end OAI
