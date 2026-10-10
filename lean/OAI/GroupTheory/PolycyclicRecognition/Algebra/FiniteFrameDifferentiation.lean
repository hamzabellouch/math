import OAI.GroupTheory.PolycyclicRecognition.Algebra.ChartedInvariantFrame

namespace OAI

/-! # Differentiability of a finite-dimensional frame -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold

variable {X E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A finite basis makes pointwise differentiability sufficient for an
operator-valued frame. -/
theorem differentiableAt_clm_of_apply {A : X → E →L[ℝ] F} {x : X}
    (hA : ∀ v : E, DifferentiableAt ℝ (fun z => A z v) x) :
    DifferentiableAt ℝ A x := by
  let b := Module.finBasis ℝ E
  have heq : A = fun z => ∑ i, ContinuousLinearMap.smulRightL ℝ E F
      (b.coord i).toContinuousLinearMap (A z (b i)) := by
    funext z
    apply ContinuousLinearMap.ext
    intro v
    change A z v = (∑ i, ContinuousLinearMap.smulRightL ℝ E F
      (b.coord i).toContinuousLinearMap (A z (b i))) v
    simp only [sum_apply]
    change A z v = ∑ i, b.coord i v • A z (b i)
    simpa only [map_sum,map_smul,Module.Basis.coord_apply] using
      (congrArg (A z) (b.sum_repr v)).symm
  rw [heq]
  apply DifferentiableAt.fun_sum
  intro i _
  exact (ContinuousLinearMap.smulRightL ℝ E F (b.coord i).toContinuousLinearMap).differentiableAt.comp x
    (hA (b i))

variable {G : Type*} [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ,E)) ⊤ G]

theorem differentiableAt_chartInvariantFrame (g : G) :
    DifferentiableAt ℝ (chartInvariantFrame g) (extChartAt (𝓘(ℝ,E)) g g) :=
  differentiableAt_clm_of_apply (differentiableAt_chartInvariantFrame_apply g)

end PolycyclicRecognition

end

end OAI
