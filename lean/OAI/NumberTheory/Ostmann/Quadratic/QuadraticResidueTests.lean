import OAI.NumberTheory.Ostmann.QuadraticSieve.PrimeJacobiCharacter
import OAI.NumberTheory.Ostmann.QuadraticCenter.StableBiasOrientation
import OAI.NumberTheory.Ostmann.Preliminaries.TailStability
import OAI.NumberTheory.Ostmann.Preliminaries.SummandTails
import OAI.NumberTheory.Ostmann.Construction.PhysicalAmplification

namespace OAI

/-! # Actual quadratic tests on complementary residue supports -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def quadraticResidueTest (p : ℕ) (t : ℤ) (r : ℕ) : ℝ :=
  (jacobiSym ((r : ℤ) - t) p : ℝ)

theorem quadraticResidueTest_abs_le (p : ℕ) (t : ℤ) (r : ℕ) :
    |quadraticResidueTest p t r| ≤ 1 := by
  rcases jacobiSym.trichotomy ((r : ℤ) - t) p with h | h | h <;>
    simp [quadraticResidueTest, h]

theorem quadraticResidueTest_eq_character (p : ℕ) [NeZero p] (t : ℤ) (r : ℕ) :
    quadraticResidueTest p t r = jacobiCharacter p ((r : ZMod p) - (t : ZMod p)) := by
  rw [quadraticResidueTest, ← jacobiCharacter_intCast]
  simp only [Int.cast_sub, Int.cast_natCast]

theorem quadraticResidueTest_sum_zero (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (t : ℤ) :
    ∑ r ∈ Finset.range p, quadraticResidueTest p t r = 0 := by
  have heq : (∑ r ∈ Finset.range p, quadraticResidueTest p t r) =
      ∑ a : ZMod p, jacobiCharacter p a := by
    apply Finset.sum_bij (fun (r : ℕ) _ => (r : ZMod p) - (t : ZMod p))
    · intro r hr
      exact Finset.mem_univ _
    · intro r hr s hs he
      have hm := (ZMod.natCast_eq_natCast_iff' r s p).mp (sub_left_injective he)
      simpa only [Nat.mod_eq_of_lt (Finset.mem_range.mp hr),
        Nat.mod_eq_of_lt (Finset.mem_range.mp hs)] using hm
    · intro a _
      refine ⟨(a + (t : ZMod p)).val, Finset.mem_range.mpr (ZMod.val_lt _), ?_⟩
      rw [ZMod.natCast_zmod_val, add_sub_cancel_right]
    · intro r hr
      exact quadraticResidueTest_eq_character p t r
  rw [heq]
  exact MulChar.sum_eq_zero_of_ne_one (jacobiCharacter_prime_ne_one p hp2)

theorem quadraticResidueTest_complement_sum_zero (A : Set ℕ) (N p : ℕ)
    [Fact p.Prime] (hp2 : p ≠ 2) (t : ℤ) :
    (∑ r ∈ tailSupport A N p, quadraticResidueTest p t r) +
      (∑ r ∈ Finset.range p \ tailSupport A N p, quadraticResidueTest p t r) = 0 := by
  rw [add_comm, Finset.sum_sdiff (tailSupport_subset A N p)]
  exact quadraticResidueTest_sum_zero p hp2 t

theorem quadraticResidueTest_mod (p : ℕ) [NeZero p] (t : ℤ) (a : ℕ) :
    quadraticResidueTest p t (a % p) = (jacobiSym ((a : ℤ) - t) p : ℝ) := by
  rw [quadraticResidueTest_eq_character, ZMod.natCast_mod,
    ← Int.cast_natCast a, ← Int.cast_sub, jacobiCharacter_intCast]

theorem quadraticResidueTest_negative (p : ℕ) [NeZero p] (t : ℤ) (a : ℕ) :
    quadraticResidueTest p t (negativeResidue p a) = (jacobiSym (-(a : ℤ) - t) p : ℝ) := by
  rw [quadraticResidueTest_eq_character]
  change jacobiCharacter p (((-(a : ZMod p)).val : ZMod p) - (t : ZMod p)) = _
  rw [ZMod.natCast_zmod_val]
  simpa only [Int.cast_sub, Int.cast_neg, Int.cast_natCast] using
    jacobiCharacter_intCast p (-(a : ℤ) - t)

theorem quadratic_positive_projection (A₀ S : Finset ℕ) (p : ℕ) [NeZero p] (t : ℤ)
    (hS : ∀ a ∈ A₀, a % p ∈ S) :
    (∑ r ∈ S, residueMass A₀ (fun _ => 1 / (A₀.card : ℝ)) p r * quadraticResidueTest p t r) =
      (∑ a ∈ A₀, (jacobiSym ((a : ℤ) - t) p : ℝ)) / A₀.card := by
  change (∑ r ∈ S, fiberMass A₀ (fun _ => 1 / (A₀.card : ℝ)) (fun a => a % p) r *
    quadraticResidueTest p t r) = _
  rw [sum_fiberMass_mul A₀ S _ _ _ hS]
  simp only [quadraticResidueTest_mod]
  rw [← Finset.mul_sum]
  ring

theorem quadratic_negative_projection (B₀ S : Finset ℕ) (p : ℕ) [NeZero p] (t : ℤ)
    (hS : ∀ b ∈ B₀, negativeResidue p b ∈ S) :
    (∑ r ∈ S, fiberMass B₀ (fun _ => 1 / (B₀.card : ℝ)) (negativeResidue p) r * quadraticResidueTest p t r) =
      (∑ b ∈ B₀, (jacobiSym (-(b : ℤ) - t) p : ℝ)) / B₀.card := by
  rw [sum_fiberMass_mul B₀ S _ _ _ hS]
  simp only [quadraticResidueTest_negative]
  rw [← Finset.mul_sum]
  ring

end Ostmann

end OAI
