import Mathlib
import OAI.Analysis.SymmetricDomains.EulerSpectrum

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open Filter Topology
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
namespace Release061
open Set Filter Topology
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def chartLeftMap (e : OpenPartialHomeomorph G E) (g : G) (x : E) : E :=
  e (g*e.symm x)

def chartLeftDensity (e : OpenPartialHomeomorph G E) (x : E) : ℝ :=
  |(fderiv ℝ (chartLeftMap e (e.symm x)) (e 1)).det|⁻¹

theorem chartLeftMap_fderiv_cocycle
    (e : OpenPartialHomeomorph G E) (he1 : 1∈e.source)
    (hC : ∀ (g : G) y, y∈e.target →
      ContDiffAt ℝ 1 (chartLeftMap e g) y)
    (g : G) (x : E) (hx : x∈e.target) (_hg : g*e.symm x∈e.source) :
    fderiv ℝ (chartLeftMap e (g*e.symm x)) (e 1) =
      (fderiv ℝ (chartLeftMap e g) x).comp
        (fderiv ℝ (chartLeftMap e (e.symm x)) (e 1)) := by
  have hbase := e.map_source he1
  have hax : chartLeftMap e (e.symm x) (e 1)=x := by
    simp only [chartLeftMap,e.left_inv he1,mul_one,e.right_inv hx]
  have hdx := (hC (e.symm x) (e 1) hbase).differentiableAt (by simp)
  have hdg := (hC g x hx).differentiableAt (by simp)
  have ht : ∀ᶠ t in 𝓝 (e 1), e.symm x*e.symm t∈e.source := by
    have hc : ContinuousAt (fun t => e.symm x*e.symm t) (e 1) :=
      continuousAt_const.mul (e.symm.continuousAt hbase)
    have hv : e.symm x*e.symm (e 1)∈e.source := by
      simpa only [e.left_inv he1,mul_one] using e.map_target hx
    exact hc.preimage_mem_nhds (e.open_source.mem_nhds hv)
  have heq : (chartLeftMap e g ∘ chartLeftMap e (e.symm x)) =ᶠ[𝓝 (e 1)]
      chartLeftMap e (g*e.symm x) := by
    filter_upwards [ht] with t ht
    simp only [chartLeftMap,Function.comp_apply,e.left_inv ht,mul_assoc]
  have hdg' : HasFDerivAt (chartLeftMap e g) (fderiv ℝ (chartLeftMap e g) x)
      (chartLeftMap e (e.symm x) (e 1)) := by rw [hax]; exact hdg.hasFDerivAt
  have hc := (hdg'.comp (e 1) hdx.hasFDerivAt).congr_of_eventuallyEq heq.symm
  exact hc.fderiv

theorem chartLeftDensity_jacobian
    (e : OpenPartialHomeomorph G E) (he1 : 1∈e.source)
    (hC : ∀ (g : G) y, y∈e.target →
      ContDiffAt ℝ 1 (chartLeftMap e g) y)
    (hD : ∀ (g : G) y, y∈e.target → g*e.symm y∈e.source →
      (fderiv ℝ (chartLeftMap e g) y).det ≠ 0)
    (g : G) (x : E) (hx : x∈e.target) (hg : g*e.symm x∈e.source) :
    chartLeftDensity e (chartLeftMap e g x) *
      |(fderiv ℝ (chartLeftMap e g) x).det| = chartLeftDensity e x := by
  have hcomp := chartLeftMap_fderiv_cocycle e he1 hC g x hx hg
  have heq : e.symm (chartLeftMap e g x)=g*e.symm x := e.left_inv hg
  have hd := hD g x hx hg
  unfold chartLeftDensity
  rw [heq,hcomp]
  simp only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp,abs_mul]
  rw [mul_inv_rev,mul_assoc,inv_mul_cancel₀ (abs_ne_zero.mpr hd),mul_one]

end Release061

end

end OAI
