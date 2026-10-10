import Mathlib
import OAI.Analysis.SymmetricDomains.ChartLeftDensityJacobian

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
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
include hU
omit [LocallyCompactSpace U] in

theorem projected_chart_left_differential_apply
    (p : U) (P : (Affine n × (Affine n →L[ℂ] Affine n)) →L[ℝ] E)
    (e : OpenPartialHomeomorph (Biholomorph U U) E)
    (he : (e : Biholomorph U U → E)=(fun a => P (ambientFirstJet p a)))
    (he1 : 1∈e.source)
    (L : E →L[ℝ] (Affine n × (Affine n →L[ℂ] Affine n)))
    (hL : HasStrictFDerivAt (fun t => ambientFirstJet p (e.symm t)) L (e 1))
    (g : Biholomorph U U) (v : E) :
    (fderiv ℝ (chartLeftMap e g) (e 1)) v =
      P (g.derivativeAt p (L v).1,
        (fderiv ℂ (fderiv ℂ g.ambientAut) p.val) (L v).1 +
          (g.derivativeAt p).comp (L v).2) := by
  have hy : (e.symm (e 1)).ambientAut p.val=p.val := by
    rw [e.left_inv he1]
    simp only [ambientAut_apply,one_apply]
  have hid : fderiv ℂ (e.symm (e 1)).ambientAut p.val=1 := by
    change (e.symm (e 1)).derivativeAt p=1
    rw [e.left_inv he1,derivativeAt_one hU]
  have hA := ((g.ambientAut_analytic hU p.val p.property).hasStrictFDerivAt).restrictScalars ℝ
  have hD := ((g.ambientAut_analytic hU p.val p.property).fderiv.hasStrictFDerivAt).restrictScalars ℝ
  have hA' : HasStrictFDerivAt g.ambientAut ((g.derivativeAt p).restrictScalars ℝ)
      ((e.symm (e 1)).ambientAut p.val) := by rw [hy]; exact hA
  have hD' : HasStrictFDerivAt (fderiv ℂ g.ambientAut)
      ((fderiv ℂ (fderiv ℂ g.ambientAut) p.val).restrictScalars ℝ)
      ((e.symm (e 1)).ambientAut p.val) := by rw [hy]; exact hD
  have hAv := hA'.comp (e 1) hL.fst
  have hDv := hD'.comp (e 1) hL.fst
  let B := (ContinuousLinearMap.compL ℂ (Affine n) (Affine n) (Affine n)).bilinearRestrictScalars ℝ
  have hB := (B.isBoundedBilinearMap.hasStrictFDerivAt
    (fderiv ℂ g.ambientAut ((e.symm (e 1)).ambientAut p.val),
      (e.symm (e 1)).derivativeAt p)).comp (e 1) (hDv.prodMk hL.snd)
  have hpair := hAv.prodMk hB
  have hj : (fun t => ambientFirstJet p (g*e.symm t)) =
      (fun t => (g.ambientAut ((e.symm t).ambientAut p.val),
        (fderiv ℂ g.ambientAut ((e.symm t).ambientAut p.val)).comp ((e.symm t).derivativeAt p))) := by
    funext t
    apply Prod.ext
    · simp only [ambientFirstJet,ambientAut_apply,mul_apply]
    · simpa only [ambientFirstJet,ambientAut_apply,derivativeAt] using derivativeAt_mul hU g (e.symm t) p
  have hPc := ContinuousLinearMap.hasStrictFDerivAt (𝕜 := ℝ)
    (E := Affine n × (Affine n →L[ℂ] Affine n)) (F := E)
    (x := (g.ambientAut ((e.symm (e 1)).ambientAut p.val),
      (fderiv ℂ g.ambientAut ((e.symm (e 1)).ambientAut p.val)).comp
        ((e.symm (e 1)).derivativeAt p))) P
  have hp := HasStrictFDerivAt.comp (𝕜 := ℝ) (E := E)
    (F := Affine n × (Affine n →L[ℂ] Affine n)) (G := E) (e 1) hPc hpair
  have hf := hp.hasFDerivAt.congr_of_eventuallyEq (f₁ := chartLeftMap e g) (by
    filter_upwards [] with t
    rw [chartLeftMap,he]
    dsimp only
    rw [congrFun hj t]
    rfl)
  rw [hf.fderiv]
  simp [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.one_def,
    IsBoundedBilinearMap.deriv, B,hy,hid,derivativeAt,add_comm]
end Biholomorph
end Release061

end

end OAI
