import Mathlib

namespace OAI


namespace Problem355.UnitPivot

variable {R : Type*} [CommRing R]
variable {m n : Type*}

def MinorsVanish (A : Matrix m n R) : Prop :=
  ∀ i k j l, A i j * A k l = A i l * A k j

theorem entry_eq_of_pivot_minor (A : Matrix m n R) (p : m) (q : n)
    (u : Rˣ) (hp : A p q = (u : R)) (i : m) (j : n)
    (hminor : A p q * A i j = A i q * A p j) :
    A i j = A i q * (↑(u⁻¹) : R) * A p j := by
  calc
    A i j = (↑(u⁻¹) : R) * ((u : R) * A i j) := by simp
    _ = (↑(u⁻¹) : R) * (A i q * A p j) := by rw [← hp, hminor]
    _ = A i q * (↑(u⁻¹) : R) * A p j := by ring

theorem minorsVanish_iff_pivot (A : Matrix m n R) (p : m) (q : n)
    (u : Rˣ) (hp : A p q = (u : R)) :
    MinorsVanish A ↔ ∀ i j, A p q * A i j = A i q * A p j := by
  constructor
  · intro h i j
    simpa [mul_comm] using h p i q j
  · intro h i k j l
    rw [entry_eq_of_pivot_minor A p q u hp i j (h i j),
      entry_eq_of_pivot_minor A p q u hp k l (h k l),
      entry_eq_of_pivot_minor A p q u hp i l (h i l),
      entry_eq_of_pivot_minor A p q u hp k j (h k j)]
    ring

theorem minorsVanish_iff_entries (A : Matrix m n R) (p : m) (q : n)
    (u : Rˣ) (hp : A p q = (u : R)) :
    MinorsVanish A ↔
      ∀ i j, A i j = A i q * (↑(u⁻¹) : R) * A p j := by
  constructor
  · intro h i j
    exact entry_eq_of_pivot_minor A p q u hp i j
      ((minorsVanish_iff_pivot A p q u hp).mp h i j)
  · intro h i k j l
    rw [h i j, h k l, h i l, h k j]
    ring

theorem eq_of_pivot_row_column (A C : Matrix m n R) (p : m) (q : n)
    (u : Rˣ) (hp : A p q = (u : R))
    (hA : MinorsVanish A) (hC : MinorsVanish C)
    (hrow : ∀ j, A p j = C p j) (hcol : ∀ i, A i q = C i q) :
    A = C := by
  have hpC : C p q = (u : R) := (hrow q).symm.trans hp
  ext i j
  rw [(minorsVanish_iff_entries A p q u hp).mp hA i j,
    (minorsVanish_iff_entries C p q u hpC).mp hC i j,
    hcol i, hrow j]

end Problem355.UnitPivot

end OAI
