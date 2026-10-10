import OAI.Combinatorics.SphericalRamsey.Coloring
import OAI.Combinatorics.SphericalRamsey.EnergyIdentity
import Lean.Elab.Tactic.Omega

namespace OAI

noncomputable section
open scoped BigOperators
namespace GrahamSpherical

/-- The actual finite squared Euclidean energy of the entrywise derivation. -/
def derivationEnergy {n : ℕ} (D : Derivation ℤ ℝ ℝ) (y : Point n) : ℝ :=
  ∑ j : Fin n, (D (y j)) ^ 2

/-- Native integer floor and Euclidean remainder, reindexed into Fin 50. -/
def energyColor {n : ℕ} (e : Point n → ℝ) (y : Point n) : Fin 50 :=
  ⟨((Int.floor (3 * e y)) % 50).toNat, by
    have h0 := Int.emod_nonneg (Int.floor (3 * e y)) (by norm_num : (50 : ℤ) ≠ 0)
    have hlt := Int.emod_lt_of_pos (Int.floor (3 * e y)) (by norm_num : (0 : ℤ) < 50)
    omega⟩

theorem energyColor_eq_implies_residue_eq {n : ℕ} (e : Point n → ℝ)
    (x y : Point n) (h : energyColor e x = energyColor e y) :
    (Int.floor (3 * e x)) % 50 = (Int.floor (3 * e y)) % 50 := by
  have he := congrArg Fin.val h
  change ((Int.floor (3 * e x)) % 50).toNat =
    ((Int.floor (3 * e y)) % 50).toNat at he
  have hx := Int.emod_nonneg (Int.floor (3 * e x)) (by norm_num : (50 : ℤ) ≠ 0)
  have hy := Int.emod_nonneg (Int.floor (3 * e y)) (by norm_num : (50 : ℤ) ≠ 0)
  omega

/-- Every copy here is an actual isometry of the literal witness subtype.
The energy identity is an explicit intermediate premise, discharged separately. -/
theorem energyColor_avoids_of_invariant {n : ℕ} (e : Point n → ℝ)
    (hinvariant : ∀ (f : witness → Point n), Isometry f →
      ∑ i : Label, (weight i : ℝ) * e (f ⟨vertex i, ⟨i, rfl⟩⟩) = 8) :
    AvoidsCopy witness (energyColor e) := by
  rintro ⟨f, hf, c, hc⟩
  have hi := hinvariant f hf
  obtain ⟨i, j, hij⟩ := rounding_obstruction
    (fun i : Label => e (f ⟨vertex i, ⟨i, rfl⟩⟩)) (by
      simpa [weight] using hi)
  apply hij
  apply energyColor_eq_implies_residue_eq e
  exact (hc ⟨vertex i, ⟨i, rfl⟩⟩).trans (hc ⟨vertex j, ⟨j, rfl⟩⟩).symm

end GrahamSpherical

end

end OAI
