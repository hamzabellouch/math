import OAI.MeasureTheory.Falconer.Geometry.TubeFiberCoordinates

namespace OAI

/-! Select original cell representatives for the scalar row set of a
regular tube fiber. No new projected row labels are introduced. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem regular_coordinate_rows {δ τ K : ℝ} (hδ : 0 < δ)
    (hτ : 0 ≤ τ) (hK : 1 ≤ K) (l : Space 2) (hl : |l 0| ≤ 1)
    (S : Finset (Space 2)) (hS : S.Nonempty) (hchart : InBoundedLineChart S)
    (hsep : FiniteSeparatedAt δ S) (hinc : ∀ p ∈ S, TubeIncident δ p l)
    (hreg : NormalizedFiniteBallBound δ τ K S) :
    let Y := S.image fun p => p 0
    Y.Nonempty ∧ (S.card:ℝ) ≤ 25*(Y.card:ℝ) ∧
      (∀ u r : ℝ, δ ≤ r → r ≤ 1 →
        scalarBallMass Y u r ≤ (25*K*(4:ℝ)^τ)*r^τ*(Y.card:ℝ)) ∧
      ∃ c : ℝ → Space 2, ∀ y ∈ Y, c y ∈ S ∧ c y 0 = y ∧ |y| ≤ 1 := by
  let Y := S.image fun p => p 0
  have hrep (y : ℝ) (hy : y ∈ Y) : ∃ p ∈ S, p 0 = y := Finset.mem_image.mp hy
  let c := fun y => if hy : y ∈ Y then Classical.choose (hrep y hy) else 0
  refine ⟨hS.image _,tube_point_coordinate_card hδ l hl S hsep hinc,
    tube_point_coordinates_regular hδ hτ hK l hl S hsep hinc hreg,c,?_⟩
  intro y hy
  have hh := Classical.choose_spec (hrep y hy)
  have he : c y = Classical.choose (hrep y hy) := dite_eq_left hy
  refine ⟨he ▸ hh.1,he ▸ hh.2,?_⟩
  rw [← hh.2]
  exact (hchart _ hh.1).1

end Falconer

end OAI
