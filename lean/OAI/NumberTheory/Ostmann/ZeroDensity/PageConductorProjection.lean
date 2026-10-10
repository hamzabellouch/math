import OAI.NumberTheory.Ostmann.ZeroDensity.PageSelection
import OAI.NumberTheory.Ostmann.ZeroDensity.ConductorDeletion

namespace OAI

/-! # The selected Page correction factors through the frequency modulus -/

namespace Ostmann

open Classical

/-- After excluding a selected large conductor prime, the correction on
the full modulus is exactly its correction on the frequency modulus. -/
theorem pageAtModulus_mul_eq (z : Option PrimitiveRealZero) (Q R T : ℕ)
    (hQ : ∀ p, p.Prime → p ∣ Q → p < T)
    (hR : ∀ p, p.Prime → p ∣ R → T ≤ p)
    (hexcluded : ∀ e, z = some e → ∀ p,
      deletedConductorPrime e.modulus T = some p → ¬p ∣ R) :
    pageAtModulus (Q * R) z = pageAtModulus Q z := by
  cases z with
  | none => rfl
  | some e =>
    by_cases hd : e.modulus ∣ Q * R
    · have hf := conductor_dvd_frequency_of_deletion e.modulus Q R T hQ hR
        (hexcluded e rfl) hd
      simp [pageAtModulus, hd, hf]
    · have hf : ¬e.modulus ∣ Q := fun h => hd (dvd_mul_of_dvd_left h R)
      simp [pageAtModulus, hd, hf]

/-- The character value itself depends only on the smaller residue. This
is the arithmetic justification for keeping the Page factor in the
frequency-coordinate average when applying CRT. -/
theorem pageCoefficient_eq_of_modEq (z : Option PrimitiveRealZero) {Q a b : ℕ}
    (hab : Nat.ModEq Q a b) :
    pageCoefficient (pageAtModulus Q z) a = pageCoefficient (pageAtModulus Q z) b := by
  cases z with
  | none => rfl
  | some e =>
    by_cases hd : e.modulus ∣ Q
    · have heq : (a : ZMod e.modulus) = (b : ZMod e.modulus) :=
        (ZMod.natCast_eq_natCast_iff a b e.modulus).mpr (hab.of_dvd hd)
      simp only [pageAtModulus, Option.bind_some, ite_eq_left hd, pageCoefficient, heq]
    · simp [pageAtModulus, hd, pageCoefficient]

theorem selectedPageCorrection_frequency (P : PublishedProgressionInput) (N Q R T : ℕ)
    (hQ : ∀ p, p.Prime → p ∣ Q → p < T)
    (hR : ∀ p, p.Prime → p ∣ R → T ≤ p)
    (hexcluded : ∀ e, selectedPageZero P N = some e → ∀ p,
      deletedConductorPrime e.modulus T = some p → ¬p ∣ R)
    {a b : ℕ} (hab : Nat.ModEq Q a b) :
    pageCoefficient (pageAtModulus (Q * R) (selectedPageZero P N)) a =
      pageCoefficient (pageAtModulus (Q * R) (selectedPageZero P N)) b := by
  rw [pageAtModulus_mul_eq (selectedPageZero P N) Q R T hQ hR hexcluded]
  exact pageCoefficient_eq_of_modEq _ hab

end Ostmann

end OAI
