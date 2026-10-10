import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSampledProbeFrames
import OAI.GroupTheory.PolycyclicRecognition.Geometry.GradedHeight

namespace OAI

/-! # A total profile base point at the moving physical pivot -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra Set Filter
open scoped Manifold Topology

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsTopologicalGroup G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype I] [DecidableEq I]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)

omit [IsTopologicalGroup G] in
/-- Only the finite initial segment uses a fallback. Eventually the total
subtype-valued base point is the exact physical pivot, with its unchanged
height. No extra base point membership hypothesis is needed for small scales. -/
theorem CartanFactorModel.exists_profile_pivot
    (X : I → H) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    (h : H →ₗ[ℝ] W) (hh : ∀ x y : H, h ⁅x, y⁆ = 0)
    (scale : ℕ → ℝ) (hs0 : ∀ n, 0 < scale n) (pivot : H)
    (Z : Set (Fin (finrank ℝ H) → ℝ))
    (hp : ∀ᶠ n in atTop,
      (exponentialRescaleBasis (WordBasisSelections.basis X S β)
        (fun j => bracketWordExponent (fun _ : I => 1) (β.val j))
        (Real.log (scale n))).equivFun (scale n • pivot) ∈ Z) :
    let b := WordBasisSelections.basis X S β
    let br := fun n => exponentialRescaleBasis b
      (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (Real.log (scale n))
    ∃ z₀ : ℕ → Z, ∀ᶠ n in atTop,
      (z₀ n).val = (br n).equivFun (scale n • pivot) ∧
      F.profileChart (br n) (z₀ n).val =
        Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∧
      h (b.equivFun.symm (z₀ n).val) = h pivot := by
  classical
  dsimp only
  let b := WordBasisSelections.basis X S β
  let br := fun n => exponentialRescaleBasis b
    (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (Real.log (scale n))
  have hne : Nonempty Z := by
    obtain ⟨n, hn⟩ := hp.exists
    exact ⟨⟨(br n).equivFun (scale n • pivot), hn⟩⟩
  let z₀ : ℕ → Z := fun n =>
    if hz : (br n).equivFun (scale n • pivot) ∈ Z
    then ⟨(br n).equivFun (scale n • pivot), hz⟩ else Classical.choice hne
  refine ⟨z₀, ?_⟩
  filter_upwards [hp] with n hn
  have hz : (z₀ n).val = (br n).equivFun (scale n • pivot) := by
    dsimp only [z₀]
    split
    · rfl
    · rename_i hz
      exact (hz hn).elim
  refine ⟨hz, ?_, ?_⟩
  · rw [hz, F.profileChart_coordinates]
    exact F.compatibleD _
  · rw [hz]
    exact word_length_chart_pivot_height X S β h hh (hs0 n) pivot

end PolycyclicRecognition

end

end OAI
