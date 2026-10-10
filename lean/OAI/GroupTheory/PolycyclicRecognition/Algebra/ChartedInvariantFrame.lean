import OAI.GroupTheory.PolycyclicRecognition.Algebra.ChartedVectorFieldBracket
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SmoothExponentialCurve
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

/-! # A left-invariant frame in a fixed chart

Linearity in the initial tangent vector lets a finite basis handle a
varying tangent parameter with only first derivatives of the frame.
-/

noncomputable section
namespace PolycyclicRecognition

open Filter Function
open scoped Manifold Topology

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]

def chartInvariantFrame (g₀ : G) (z : E) : E →L[ℝ] E :=
  ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (extChartAt (𝓘(ℝ, E)) g₀).symm z).inverse).comp
    (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E))
      (fun h : G => (extChartAt (𝓘(ℝ, E)) g₀).symm z * h) 1)

omit [LieGroup (𝓘(ℝ, E)) ⊤ G] in
theorem chartInvariantFrame_apply (g₀ : G) (z v : E) :
    chartInvariantFrame g₀ z v =
      chartVectorField g₀ (mulInvariantVectorField (I := 𝓘(ℝ, E)) v) z := rfl

@[simp] theorem chartInvariantFrame_one :
    chartInvariantFrame (1 : G) (extChartAt (𝓘(ℝ, E)) (1 : G) 1) =
      ContinuousLinearMap.id ℝ E := by
  unfold chartInvariantFrame
  rw [mfderiv_chart_symm_base]
  have heq : (fun h : G => (extChartAt (𝓘(ℝ, E)) (1 : G)).symm
      (extChartAt (𝓘(ℝ, E)) (1 : G) 1) * h) = id := by
    ext h
    rw [extChartAt_to_inv, one_mul]
    rfl
  rw [heq, mfderiv_id]
  change (ContinuousLinearMap.id ℝ E).inverse.comp (ContinuousLinearMap.id ℝ E) = _
  rw [ContinuousLinearMap.inverse_id, ContinuousLinearMap.id_comp]

theorem differentiableAt_chartInvariantFrame_apply [CompleteSpace E]
    (g₀ : G) (v : E) :
    DifferentiableAt ℝ (fun z => chartInvariantFrame g₀ z v)
      (extChartAt (𝓘(ℝ, E)) g₀ g₀) :=
  differentiableAt_chartVectorField
    ((contMDiff_invariantVectorField_infty (E := E) v g₀).mdifferentiableAt (by simp))

theorem differentiableAt_chartInvariantFrame_parameter [FiniteDimensional ℝ E]
    {a : ℝ → E} {t : ℝ} (ha : DifferentiableAt ℝ a t) (g₀ : G) :
    DifferentiableAt ℝ (fun q : ℝ × E => chartInvariantFrame g₀ q.2 (a q.1))
      (t, extChartAt (𝓘(ℝ, E)) g₀ g₀) := by
  let b := Module.finBasis ℝ E
  have heq : (fun q : ℝ × E => chartInvariantFrame g₀ q.2 (a q.1)) =
      (fun q => ∑ i, (b.coord i (a q.1)) • chartInvariantFrame g₀ q.2 (b i)) := by
    funext q
    conv_lhs => rw [← b.sum_repr (a q.1)]
    simp only [map_sum, map_smul, Module.Basis.coord_apply]
  rw [heq]
  apply DifferentiableAt.fun_sum
  intro i _
  have hcoeff : DifferentiableAt ℝ (fun q : ℝ × E => b.coord i (a q.1))
      (t, extChartAt (𝓘(ℝ, E)) g₀ g₀) :=
    ((b.coord i).toContinuousLinearMap.differentiableAt).comp _
      (ha.comp _ differentiableAt_fst)
  have hframe : DifferentiableAt ℝ (fun z : E => chartInvariantFrame g₀ z (b i))
      (extChartAt (𝓘(ℝ, E)) g₀ g₀) :=
    differentiableAt_chartInvariantFrame_apply g₀ (b i)
  have hfr : DifferentiableAt ℝ (fun q : ℝ × E => chartInvariantFrame g₀ q.2 (b i))
      (t, extChartAt (𝓘(ℝ, E)) g₀ g₀) :=
    hframe.comp (t, extChartAt (𝓘(ℝ, E)) g₀ g₀) (f := fun q : ℝ × E => q.2)
      differentiableAt_snd
  exact hcoeff.smul hfr

end PolycyclicRecognition

end

end OAI
