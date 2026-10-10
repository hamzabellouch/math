import OAI.Analysis.KadisonKastler.Polar
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

namespace OAI

/-!
# Passing an intertwiner to its polar unitary

An invertible intertwiner of star representations has a unitary polar
factor which intertwines the same representations. Combining this with
the polar estimate gives the near-identity unitary used in the manuscript.
-/

namespace KadisonKastler

open scoped CStarAlgebra

variable {S B : Type*} [Ring S] [StarRing S] [Algebra ℂ S] [CStarAlgebra B]

/-- Taking adjoints reverses the intertwining relation. -/
theorem star_intertwines (ρ θ : S →⋆ₐ[ℂ] B) {T : B}
    (hT : ∀ x, T * ρ x = θ x * T) (x : S) :
    star T * θ x = ρ x * star T := by
  have h := congrArg star (hT (star x))
  simpa only [star_mul, map_star, star_star] using h.symm

/-- The square of the absolute value of an intertwiner commutes with the
source representation. -/
theorem intertwiner_star_mul_self_commute (ρ θ : S →⋆ₐ[ℂ] B) {T : B}
    (hT : ∀ x, T * ρ x = θ x * T) (x : S) :
    Commute (star T * T) (ρ x) := by
  change (star T * T) * ρ x = ρ x * (star T * T)
  calc
    (star T * T) * ρ x = star T * (T * ρ x) := mul_assoc _ _ _
    _ = star T * (θ x * T) := by rw [hT]
    _ = (star T * θ x) * T := (mul_assoc _ _ _).symm
    _ = (ρ x * star T) * T := by rw [star_intertwines ρ θ hT]
    _ = ρ x * (star T * T) := mul_assoc _ _ _

section Ordered

variable [PartialOrder B] [StarOrderedRing B]

/-- Continuous functional calculus passes the intertwiner commutation
relation to its absolute value. -/
theorem intertwiner_abs_commute (ρ θ : S →⋆ₐ[ℂ] B) {T : B}
    (hT : ∀ x, T * ρ x = θ x * T) (x : S) :
    Commute (CFC.abs T) (ρ x) := by
  exact (intertwiner_star_mul_self_commute ρ θ hT x).cfcₙ_nnreal NNReal.sqrt

/-- A unitary factor in the polar decomposition of an invertible
intertwiner remains an intertwiner. -/
theorem polar_unitary_intertwines (ρ θ : S →⋆ₐ[ℂ] B) {T : B}
    (hunit : IsUnit T) (hT : ∀ x, T * ρ x = θ x * T)
    (u : unitary B) (hpolar : (u : B) * CFC.abs T = T) (x : S) :
    (u : B) * ρ x = θ x * (u : B) := by
  have habs : IsUnit (CFC.abs T) := by
    obtain ⟨t, rfl⟩ := hunit
    exact isUnit_abs t
  apply habs.mul_right_cancel
  calc
    ((u : B) * ρ x) * CFC.abs T = (u : B) * (ρ x * CFC.abs T) := mul_assoc _ _ _
    _ = (u : B) * (CFC.abs T * ρ x) := by rw [(intertwiner_abs_commute ρ θ hT x).eq]
    _ = ((u : B) * CFC.abs T) * ρ x := (mul_assoc _ _ _).symm
    _ = θ x * T := by rw [hpolar, hT]
    _ = (θ x * (u : B)) * CFC.abs T := by rw [mul_assoc, hpolar]

end Ordered

/-- A near-identity star intertwiner produces a near-identity unitary
intertwiner. Only the existence of the original intertwiner is assumed. -/
theorem exists_near_unitary_intertwiner (ρ θ : S →⋆ₐ[ℂ] B) {T : B}
    (hT : ∀ x, T * ρ x = θ x * T) (hnear : ‖T - 1‖ < 1) :
    ∃ u : unitary B, (∀ x, (u : B) * ρ x = θ x * (u : B)) ∧
      ‖(u : B) - 1‖ ≤ 2 * ‖T - 1‖ := by
  let := CStarAlgebra.spectralOrder B
  let := CStarAlgebra.spectralOrderedRing B
  nontriviality B
  have hunit : IsUnit T := (Units.ofNearby 1 T (by simpa using hnear)).isUnit
  obtain ⟨u, hpolar, hnorm⟩ := exists_polar_unitary_near_one T hnear
  exact ⟨u, polar_unitary_intertwines ρ θ hunit hT u hpolar, hnorm⟩

/-- Unitary conjugation obtained from a near-identity star intertwiner. -/
theorem exists_near_unitary_conjugating (ρ θ : S →⋆ₐ[ℂ] B) {T : B}
    (hT : ∀ x, T * ρ x = θ x * T) (hnear : ‖T - 1‖ < 1) :
    ∃ u : unitary B, (∀ x, (u : B) * ρ x * star (u : B) = θ x) ∧
      ‖(u : B) - 1‖ ≤ 2 * ‖T - 1‖ := by
  obtain ⟨u, hu, hnorm⟩ := exists_near_unitary_intertwiner ρ θ hT hnear
  refine ⟨u, ?_, hnorm⟩
  intro x
  rw [hu, mul_assoc, Unitary.mul_star_self_of_mem u.property, mul_one]

end KadisonKastler

end OAI
