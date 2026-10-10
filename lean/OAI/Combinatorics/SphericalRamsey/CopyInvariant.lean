import OAI.Combinatorics.SphericalRamsey.MonochromaticObstruction
import OAI.Combinatorics.SphericalRamsey.AffineCopy

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace GrahamSpherical

/-- All distance-preserving copies, with no affine-form or dimension premise. -/
theorem weighted_copy_derivation_energy {n : ℕ}
    (D : Derivation ℤ ℝ ℝ)
    (hD : D parameter = (1 + parameter ^ 2) / 2)
    (f : witness → Point n) (hf : Isometry f) :
    ∑ i : Label, (weight i : ℝ) *
      derivationEnergy D (f ⟨vertex i, ⟨i, rfl⟩⟩) = 8 := by
  let y : Label → Point n := fun i => f ⟨vertex i, ⟨i, rfl⟩⟩
  have hy : ∀ i j, dist (y i) (y j) = dist (vertex i) (vertex j) := by
    intro i j
    exact hf.dist_eq ⟨vertex i, ⟨i, rfl⟩⟩ ⟨vertex j, ⟨j, rfl⟩⟩
  obtain ⟨z, A, B, hA, hB, _hAB, hform⟩ := affine_copy y hy
  have hAs : ∑ j : Fin n, A j ^ 2 = 1 := (sum_sq_eq_inner A).trans hA
  have hBs : ∑ j : Fin n, B j ^ 2 = 1 := (sum_sq_eq_inner B).trans hB
  have hpoint (i : Label) (j : Fin n) :
      y i j = z j + coordinates i 0 * A j + coordinates i 1 * B j := by
    have h := congrArg (fun x : Point n => x j) (hform i)
    simpa using h
  have henergy (i : Label) : derivationEnergy D (y i) =
      ∑ j : Fin n, (D (z j + coordinates i 0 * A j + coordinates i 1 * B j)) ^ 2 := by
    unfold derivationEnergy
    simp_rw [hpoint]
  change (∑ i : Label, (weight i : ℝ) * derivationEnergy D (y i)) = 8
  simp_rw [henergy]
  exact weighted_affine_derivation_energy D hD z A B hAs hBs

theorem derivationColor_avoids {n : ℕ}
    (D : Derivation ℤ ℝ ℝ)
    (hD : D parameter = (1 + parameter ^ 2) / 2) :
    AvoidsCopy witness (energyColor (derivationEnergy (n := n) D)) :=
  energyColor_avoids_of_invariant _ (weighted_copy_derivation_energy D hD)

end GrahamSpherical

end

end OAI
