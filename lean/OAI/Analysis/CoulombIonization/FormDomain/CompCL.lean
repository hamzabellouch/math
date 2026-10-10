import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.L2

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
open MeasureTheory Filter
open scoped ENNReal
namespace CoulombSobolev.Test
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def compCL (φ : Test F) (e : E ≃L[ℝ] F) : Test E where
  fn x := φ.fn (e x)
  smooth := φ.smooth.comp e.contDiff
  compact := φ.compact.comp_homeomorph e.toHomeomorph

lemma ext_fn {φ η : Test E} (h : φ.fn = η.fn) : φ = η := by
  cases φ; cases η; cases h; rfl

lemma compCL_deriv (φ : Test F) (e : E ≃L[ℝ] F) (v : E) :
    (φ.compCL e).deriv v = (φ.deriv (e v)).compCL e := by
  apply ext_fn
  funext x
  change fderiv ℝ (φ.fn ∘ e) x v = _
  rw [fderiv_comp x (φ.smooth.differentiable (by simp) _) e.differentiableAt]
  simp only [ContinuousLinearEquiv.fderiv, ContinuousLinearMap.comp_apply]
  rfl
end CoulombSobolev.Test

end

end OAI
