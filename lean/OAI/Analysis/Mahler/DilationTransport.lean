import OAI.Analysis.Mahler.ExteriorFlux
import OAI.Analysis.Mahler.WedgeAlgebra

namespace OAI

open Complex ContinuousAlternatingMap Filter
open scoped Topology
namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

noncomputable def realDilation (r : ℝ) : E →L[ℝ] E := r • ContinuousLinearMap.id ℝ E
omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
@[simp] lemma realDilation_apply [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] (r : ℝ) (x : E) : realDilation r x = r • x := rfl

lemma dcLinear_dilation {u : E → ℂ} {r : ℝ} {x : E}
    (hu : DifferentiableAt ℝ u (r • x)) (v : E) :
    dcLinear (fun y => u (r • y)) x v = dcLinear u (r • x) (r • v) := by
  have hd := hu.hasFDerivAt.comp x (realDilation r).hasFDerivAt
  change HasFDerivAt (fun y => u (r • y)) _ x at hd
  simp only [dcLinear_apply, dc]
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, realDilation_apply]
  rw [smul_comm r I v]

lemma dcLinear_sub_const (u : E → ℂ) (c : ℂ) (x : E) :
    dcLinear (fun y => u y - c) x = dcLinear u x := by
  unfold dcLinear
  congr 2
  exact fderiv_sub_const c

/-- The full shuffle boundary form, using actual exterior differentiation. -/
noncomputable def boundaryForm (u : E → ℂ) (k : ℕ) (x : E) :
    E [⋀^Fin 1 ⊕ WedgePowerSlots k]→ₗ[ℝ] ℂ :=
  wedge (oneForm (dcLinear u) x).toAlternatingMap
    (wedgePower (extDeriv (oneForm (dcLinear u)) x).toAlternatingMap k)

lemma oneForm_dilation_eventually {u : E → ℂ} {r : ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u (r • x)) :
    oneForm (dcLinear (fun y => u (r • y))) =ᶠ[𝓝 x]
      (fun y => (oneForm (dcLinear u) (r • y)).compContinuousLinearMap (realDilation r)) := by
  have hev : ∀ᶠ y in 𝓝 (r • x), DifferentiableAt ℝ u y :=
    (hu.eventually (by norm_num)).mono (fun y hy => hy.differentiableAt (by norm_num))
  have hc : Tendsto (fun y : E => r • y) (𝓝 x) (𝓝 (r • x)) :=
    (realDilation r).continuous.continuousAt
  filter_upwards [hc.eventually hev] with y hy
  ext v
  exact dcLinear_dilation hy (v 0)

/-- Pullback of the actual dd^c under a real dilation. -/
theorem extDeriv_dc_dilation {u : E → ℂ} {r : ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u (r • x)) :
    extDeriv (oneForm (dcLinear (fun y => u (r • y)))) x =
      (extDeriv (oneForm (dcLinear u)) (r • x)).compContinuousLinearMap (realDilation r) := by
  have hn := extDeriv_pullback (f := realDilation r)
    (differentiableAt_oneForm (differentiableAt_dcLinear hu))
    ((realDilation r).contDiff.contDiffAt : ContDiffAt ℝ 2 (realDilation r) x)
    (by norm_num : minSmoothness ℝ 2 ≤ (2 : WithTop ℕ∞))
  simp only [ContinuousLinearMap.fderiv, realDilation_apply] at hn
  rw [← hn]
  unfold extDeriv
  rw [(oneForm_dilation_eventually hu).fderiv_eq]

/-- Every tangent slot is transported by the derivative of dilation; the
constant subtracted from the logarithm disappears from both derivatives. -/
theorem boundaryForm_dilation {u : E → ℂ} {r : ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u (r • x)) (c : ℂ) (k : ℕ) :
    boundaryForm (fun y => u (r • y) - c) k x =
      (boundaryForm u k (r • x)).compLinearMap (realDilation r).toLinearMap := by
  have he : dcLinear (fun y => u (r • y) - c) = dcLinear (fun y => u (r • y)) :=
    funext (dcLinear_sub_const _ c)
  unfold boundaryForm
  rw [he, wedge_compLinearMap, wedgePower_compLinearMap, extDeriv_dc_dilation hu]
  congr 1
  ext v
  exact dcLinear_dilation (hu.differentiableAt (by norm_num)) (v 0)

end Mahler

end OAI
