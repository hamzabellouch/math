import OAI.NumberTheory.TwoPoint.Bounds.FiniteResidueComparison
import OAI.NumberTheory.TwoPoint.Bounds.CommonResidueLift
import Mathlib.Data.Nat.Prime.Basic

namespace OAI

/-! Canonical residue coordinates for the prime-and-offset literals
occurring in a weighted matrix word. Repeated tests share one prime
coordinate, and may have different offsets. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def primeResidueModuli (P : Finset ℕ) : Fin (Fintype.card P) → ℕ :=
  fun i => ((Fintype.equivFin P).symm i).val

noncomputable def primeLiteralCoordinate (P : Finset ℕ) {n : ℕ}
    (literal : Fin n → P × ℤ) : Fin n → Fin (Fintype.card P) :=
  fun i => (Fintype.equivFin P) (literal i).1

noncomputable def primeLiteralTest (P : Finset ℕ) {n : ℕ}
    (literal : Fin n → P × ℤ) (i : Fin n)
    (z : ZMod (primeResidueModuli P (primeLiteralCoordinate P literal i))) : Bool :=
  decide (z = -((literal i).2 : ZMod (primeResidueModuli P (primeLiteralCoordinate P literal i))))

lemma primeResidueModuli_coordinate (P : Finset ℕ) {n : ℕ}
    (literal : Fin n → P × ℤ) (i : Fin n) :
    primeResidueModuli P (primeLiteralCoordinate P literal i) = (literal i).1.val := by
  simp [primeResidueModuli, primeLiteralCoordinate]

lemma primeLiteral_integer_input (P : Finset ℕ) {n : ℕ}
    (literal : Fin n → P × ℤ) (a : ℤ) (i : Fin n) :
    residueCircuitInputs (primeResidueModuli P) (primeLiteralCoordinate P literal)
      (primeLiteralTest P literal) (fun j => (a : ZMod (primeResidueModuli P j))) i =
      decide (((literal i).1.val : ℤ) ∣ a + (literal i).2) := by
  change decide ((a : ZMod (primeResidueModuli P (primeLiteralCoordinate P literal i))) =
    -((literal i).2 : ZMod (primeResidueModuli P (primeLiteralCoordinate P literal i)))) = _
  apply Bool.decide_congr
  exact (residue_offset_divisibility
    (a : ZMod (primeResidueModuli P (primeLiteralCoordinate P literal i)))
    a (literal i).2 rfl).symm.trans (by rw [primeResidueModuli_coordinate])

lemma primeResidueModuli_prime (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (i : Fin (Fintype.card P)) : (primeResidueModuli P i).Prime :=
  hP _ ((Fintype.equivFin P).symm i).property

lemma primeResidueModuli_coprime (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Pairwise (fun i j => (primeResidueModuli P i).Coprime (primeResidueModuli P j)) := by
  intro i j hij
  apply (Nat.coprime_primes (primeResidueModuli_prime P hP i)
    (primeResidueModuli_prime P hP j)).mpr
  intro he
  apply hij
  apply (Fintype.equivFin P).symm.injective
  exact Subtype.ext he

lemma primeResidueModuli_bound (P : Finset ℕ) (B : ℝ)
    (hP : ∀ p ∈ P, (p : ℝ) ≤ B) (i : Fin (Fintype.card P)) :
    (primeResidueModuli P i : ℝ) ≤ B := hP _ ((Fintype.equivFin P).symm i).property

lemma primePool_card_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (B : ℕ) (hB : ∀ p ∈ P, p ≤ B) : P.card ≤ B := by
  let f : P → Fin B := fun p => ⟨p.val - 1, by have := (hP _ p.property).pos; have := hB _ p.property; omega⟩
  have hf : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    have he : p.val - 1 = q.val - 1 := congrArg Fin.val hpq
    have hp := (hP _ p.property).pos
    have hq := (hP _ q.property).pos
    omega
  simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_le_of_injective f hf

end TwoPointCorrelations

end OAI
