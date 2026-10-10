import OAI.Combinatorics.Progressions.Fourier.FourierLawTransport
import OAI.Combinatorics.Progressions.Geometry.FiniteImageSupportTransport

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem weightedSlice_geometric_support {b n q K : ℕ}
    (s : Fin b → Fin (n + 1) → NormalizedScalarCubeSource (Fin q)) (root : Fin b → Fin (n + 1) → ℤ)
    {O F : ℝ} (hO : 0 ≤ O)
    (hroot : ∀ a j, |(root a j : ℝ)| ≤ O * (s a j).length)
    (hupper : ∀ a, (∏ j, ((s a j).length : ℝ)) ≤ F * K)
    (J : Finset (Finset (Fin q))) (hJ : ∀ S ∈ J, S.card ≤ n + 1) :
    let Q := affineTorusRadius (Fintype.card (Fin q)) (n + 1) (Fintype.card (Fin b)) (O + 1) F
    ∀ center x, (weightedSliceIntegerSource s root).weight x ≠ 0 → ∀ Z : J,
      |(weightedSliceIntegerSum s root J center x Z : ℝ) - center Z| ≤ (Q : ℝ) * K := by
  dsimp only
  intro center x hx
  let u := fun a j => cubeRootOffset (root a j) (I := Fin q)
  apply finiteImageMass_support_transport (weightedCubeIntegerSource s)
    (weightedSliceIntegerSource s root) (affineWeightedCubeIntegerSum s u (fun _ _ _ => 1) J center)
    (weightedSliceIntegerSum s root J center) (weightedSliceIntegerSum_mass s root J center)
    (fun y => ∀ Z : J, |(y Z : ℝ) - center Z| ≤ _)
    _ x hx
  intro y _ Z
  have hQ := affineWeightedCube_bound_le_torus s u (fun _ _ _ => 1) (by linarith : 0 ≤ O + 1)
    (fun a j i => cubeRootOffset_relative_bound hO (root a j) (s a j).length (hroot a j) i)
    hupper Z (hJ Z Z.property)
  exact_mod_cast (affineWeightedCubeIntegerSum_bound s u (fun _ _ _ => 1) J center y Z).trans hQ

noncomputable def boundedWeightedSliceFourierAxis {b n q K : ℕ} [NeZero K]
    (s : Fin b → Fin (n + 1) → NormalizedScalarCubeSource (Fin q)) (root : Fin b → Fin (n + 1) → ℤ)
    {O F : ℝ} (hO : 0 ≤ O)
    (hroot : ∀ a j, |(root a j : ℝ)| ≤ O * (s a j).length)
    (hupper : ∀ a, (∏ j, ((s a j).length : ℝ)) ≤ F * K)
    (J : Finset (Finset (Fin q))) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (Kmax : ℕ) (hK : K ≤ Kmax) : IntegerFourierAxis := by
  let Q := affineTorusRadius (Fintype.card (Fin q)) (n + 1) (Fintype.card (Fin b)) (O + 1) F
  exact boundedIntegerFourierAxis (weightedSliceIntegerSource s root) (weightedSliceIntegerSum s root J)
    K Q ((2 * Q + 1) * Kmax) (Nat.mul_le_mul_left _ hK)
    (weightedSlice_geometric_support s root hO hroot hupper J hJ)

end Erdos3

end

end OAI
