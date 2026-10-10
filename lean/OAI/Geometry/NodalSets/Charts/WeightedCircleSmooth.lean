import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import OAI.Geometry.NodalSets.Charts.WeightedCircleMatrix

namespace OAI

namespace Yau.Geometry
open Matrix
open scoped ContDiff
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma matrix_det_smooth (h : E → Matrix n n ℝ)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun x ↦ h x i j)) :
    ContDiff ℝ ∞ (fun x ↦ (h x).det) := by
  simp only [Matrix.det_apply']
  apply ContDiff.sum
  intro σ _
  apply contDiff_const.mul
  apply contDiff_prod
  intro i _
  exact hh (σ i) i

lemma circleWeight_smooth (h : E → Matrix n n ℝ) (rho gamma0 : E → ℝ)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun x ↦ h x i j))
    (hp : ∀ x, (h x).PosDef) (hr : ContDiff ℝ ∞ rho) (hg : ContDiff ℝ ∞ gamma0) :
    ContDiff ℝ ∞ (fun x ↦ circleWeight (h x) (rho x) (gamma0 x)) := by
  exact (hr.mul hg).div ((matrix_det_smooth h hh).sqrt (fun x ↦ (hp x).det_pos.ne'))
    (fun x ↦ (Real.sqrt_pos.mpr (hp x).det_pos).ne')

lemma weightedCircleMatrix_smooth (h : E → Matrix n n ℝ) (rho gamma0 : E → ℝ)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun x ↦ h x i j))
    (hp : ∀ x, (h x).PosDef) (hr : ContDiff ℝ ∞ rho) (hg : ContDiff ℝ ∞ gamma0)
    (i j : n ⊕ Fin 1) :
    ContDiff ℝ ∞ (fun x ↦ weightedCircleMatrix (h x) (rho x) (gamma0 x) i j) := by
  cases i <;> cases j
  · exact hh _ _
  · exact contDiff_const
  · exact contDiff_const
  · exact (circleWeight_smooth h rho gamma0 hh hp hr hg).pow 2

end
end Yau.Geometry

end OAI
