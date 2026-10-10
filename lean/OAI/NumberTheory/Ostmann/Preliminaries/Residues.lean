import Mathlib.Data.ZMod.Basic
import OAI.NumberTheory.Ostmann.Basic

namespace OAI

/-!
# Complementary residue supports

The elementary reduction in §2 of the manuscript. Only the exclusion of
composite sums is used to separate the tail supports at a prime.
-/

namespace Ostmann

/-- Residues of a summand after deleting the initial interval through `N + p`. -/
def tailResidues (A : Set ℕ) (N p : ℕ) : Set (ZMod p) :=
  (fun a : ℕ => (a : ZMod p)) '' {a | a ∈ A ∧ N + p < a}

/-- Residues of the negative of the other summand, with the same deletion. -/
def negTailResidues (B : Set ℕ) (N p : ℕ) : Set (ZMod p) :=
  (fun b : ℕ => -(b : ZMod p)) '' {b | b ∈ B ∧ N + p < b}

/-- Large sums in an eventual prime decomposition have no smaller prime divisor. -/
theorem EventuallyPrimeSumset.prime_not_dvd_large_sum {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) :
    ∃ N, ∀ p, p.Prime → ∀ a ∈ A, ∀ b ∈ B,
      N ≤ a + b → p < a + b → ¬ p ∣ a + b := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, ?_⟩
  intro p hp a ha b hb hn hlt hdvd
  have hab : (a + b).Prime := (hN _ hn).mp ⟨a, ha, b, hb, rfl⟩
  have heq : a + b = p := (hab.dvd_iff_eq (ne_of_gt hp.one_lt)).mp hdvd
  omega

/-- The two tails have disjoint images modulo every prime (§2). -/
theorem EventuallyPrimeSumset.disjoint_tail_residues {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) :
    ∃ N, ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p) := by
  obtain ⟨N, hN⟩ := h.prime_not_dvd_large_sum
  refine ⟨N, ?_⟩
  intro p hp
  apply Set.disjoint_left.mpr
  rintro z ⟨a, ⟨ha, hna⟩, rfl⟩ ⟨b, ⟨hb, hnb⟩, hz⟩
  apply hN p hp a ha b hb (by omega) (by omega)
  apply (ZMod.natCast_eq_zero_iff (a + b) p).mp
  change -(b : ZMod p) = (a : ZMod p) at hz
  rw [Nat.cast_add, ← hz]
  simp

/-- The residue-support reduction requires only unboundedness of a summand. -/
theorem tailResidues_nonempty {A : Set ℕ} (hA : A.Infinite) (N p : ℕ) :
    (tailResidues A N p).Nonempty := by
  have hnot : ¬ BddAbove A := fun h => hA (Set.finite_iff_bddAbove.mpr h)
  obtain ⟨a, ha, hlarge⟩ := (not_bddAbove_iff.mp hnot) (N + p)
  exact ⟨(a : ZMod p), a, ⟨ha, hlarge⟩, rfl⟩

theorem negTailResidues_nonempty {B : Set ℕ} (hB : B.Infinite) (N p : ℕ) :
    (negTailResidues B N p).Nonempty := by
  have hnot : ¬ BddAbove B := fun h => hB (Set.finite_iff_bddAbove.mpr h)
  obtain ⟨b, hb, hlarge⟩ := (not_bddAbove_iff.mp hnot) (N + p)
  exact ⟨-(b : ZMod p), b, ⟨hb, hlarge⟩, rfl⟩

/-- A hypothetical decomposition yields nonempty complementary supports at every prime. -/
theorem EventuallyPrimeSumset.complementary_supports {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite) :
    ∃ N, ∀ p, p.Prime → ∃ S : Set (ZMod p),
      S.Nonempty ∧ Sᶜ.Nonempty ∧ tailResidues A N p ⊆ S ∧ negTailResidues B N p ⊆ Sᶜ := by
  obtain ⟨N, hN⟩ := h.disjoint_tail_residues
  refine ⟨N, ?_⟩
  intro p hp
  refine ⟨tailResidues A N p, tailResidues_nonempty hA N p, ?_, Set.Subset.rfl, ?_⟩
  · obtain ⟨b, hb⟩ := negTailResidues_nonempty hB N p
    exact ⟨b, fun ha => Set.disjoint_left.mp (hN p hp) ha hb⟩
  · intro b hb ha
    exact Set.disjoint_left.mp (hN p hp) ha hb

end Ostmann

end OAI
