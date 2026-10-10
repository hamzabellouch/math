import Mathlib.Analysis.Analytic.Inverse
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.LinearAlgebra.Determinant
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Topology
import Mathlib.Topology.Algebra.Module.FiniteDimension

namespace OAI

section

/-! # One-dimensional analytic zero sets are Lebesgue null -/
noncomputable section
open MeasureTheory Set Filter
namespace BoltzmannNonuniqueness.Published

theorem analytic_line_ae_ne_zero {U : Set ℝ} (hU : MeasurableSet U)
    (hc : IsPreconnected U) {f : ℝ → ℝ} (hf : AnalyticOnNhd ℝ f U)
    (hne : ∃ x ∈ U, f x ≠ 0) : ∀ᵐ x ∂volume.restrict U, f x ≠ 0 := by
  rcases hf.eqOn_zero_or_eventually_ne_zero_of_preconnected hc with hz | hn
  · obtain ⟨x,hx,hfx⟩ := hne
    exact False.elim (hfx (hz hx))
  · exact ae_restrict_le_codiscreteWithin hU hn

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Analyticity of the existing inverse from the analytic inverse theorem -/

noncomputable section

open Filter
open scoped Topology

namespace BoltzmannNonuniqueness.AnalyticInverse

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem localInverse_analytic {f : E → F} {x : E} (A : E ≃L[ℝ] F)
    (ha : AnalyticAt ℝ f x) (hf : HasStrictFDerivAt f A.toContinuousLinearMap x) :
    AnalyticAt ℝ (hf.localInverse f A x) (f x) := by
  obtain ⟨p,hp⟩ := ha
  have hcoeff : p 1 = (continuousMultilinearCurryFin1 ℝ E F).symm A.toContinuousLinearMap := by
    apply (continuousMultilinearCurryFin1 ℝ E F).injective
    rw [(continuousMultilinearCurryFin1 ℝ E F).apply_symm_apply]
    exact hp.hasFDerivAt.unique hf.hasFDerivAt
  exact ((hf.toOpenPartialHomeomorph f).hasFPowerSeriesAt_symm
    hf.mem_toOpenPartialHomeomorph_source hp hcoeff).analyticAt

theorem analytic_of_eventually_left_inverse {f : E → F} {g : F → E} {x : E}
    (A : E ≃L[ℝ] F) (ha : AnalyticAt ℝ f x)
    (hf : HasStrictFDerivAt f A.toContinuousLinearMap x)
    (hg : ∀ᶠ y in 𝓝 x, g (f y) = y) : AnalyticAt ℝ g (f x) := by
  exact (localInverse_analytic A ha hf).congr (Filter.EventuallyEq.symm (hf.localInverse_unique hg))

end BoltzmannNonuniqueness.AnalyticInverse

end

end

section

/-! # Analyticity of the determinant of a finite-dimensional operator -/

noncomputable section

namespace BoltzmannNonuniqueness

theorem determinant_analyticAt {X E : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A : X → E →L[ℝ] E} {x : X} (hA : AnalyticAt ℝ A x) :
    AnalyticAt ℝ (fun y => (A y).toLinearMap.det) x := by
  classical
  let b := Module.finBasis ℝ E
  have hc (i j : Fin (Module.finrank ℝ E)) :
      AnalyticAt ℝ (fun y => b.coord i (A y (b j))) x :=
    ((b.coord i).toContinuousLinearMap.analyticAt _).comp
      (((ContinuousLinearMap.apply ℝ E (b j)).analyticAt _).comp hA)
  have he : (fun y => (A y).toLinearMap.det) =
      (fun y => (LinearMap.toMatrix b b (A y).toLinearMap).det) := by
    funext y
    exact (LinearMap.det_toMatrix b (A y).toLinearMap).symm
  rw [he]
  simp only [Matrix.det_apply']
  apply Finset.analyticAt_fun_sum
  intro p _
  apply AnalyticAt.mul analyticAt_const
  apply Finset.analyticAt_fun_prod
  intro i _
  simpa only [LinearMap.toMatrix_apply,Module.Basis.coord_apply] using! hc (p i) i

end BoltzmannNonuniqueness

end

end

end OAI
