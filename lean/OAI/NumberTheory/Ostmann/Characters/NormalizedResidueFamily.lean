import OAI.NumberTheory.Ostmann.Characters.NormalizedResidueIndicator

namespace OAI

/-! # A single family of normalized transforms for varying sampled primes -/

namespace Ostmann
open scoped Classical BigOperators

/-- The zero modulus is unused by prime samples. This total definition lets
both histories evaluate the same transform at their actual sampled prime. -/
noncomputable def normalizedResidueFamily (sets : ∀ q : ℕ, Finset (ZMod q))
    (q : ℕ) : ZMod q → ℂ :=
  if h : q = 0 then fun _ => 0 else
    letI : NeZero q := ⟨h⟩
    normalizedResidueTransform (sets q)

theorem normalizedResidueFamily_eq (sets : ∀ q : ℕ, Finset (ZMod q))
    (q : ℕ) [NeZero q] :
    normalizedResidueFamily sets q = normalizedResidueTransform (sets q) := by
  simp only [normalizedResidueFamily, dite_eq_right (NeZero.ne q)]

theorem normalizedResidueFamily_zero (sets : ∀ q : ℕ, Finset (ZMod q))
    (q : ℕ) [NeZero q] : normalizedResidueFamily sets q 0 = 0 := by
  rw [normalizedResidueFamily_eq]
  exact normalizedResidueTransform_zero _

theorem normalizedResidueFamily_energy (sets : ∀ q : ℕ, Finset (ZMod q))
    (q : ℕ) [NeZero q] (h : (sets q).Nonempty) (hcard : (sets q).card < q) :
    (∑ z : ZMod q, ‖normalizedResidueFamily sets q z‖ ^ 2) = q := by
  rw [normalizedResidueFamily_eq]
  exact normalizedResidueTransform_energy _ h hcard

end Ostmann

end OAI
