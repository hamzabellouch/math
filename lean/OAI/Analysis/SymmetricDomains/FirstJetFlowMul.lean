import Mathlib
import OAI.Analysis.SymmetricDomains.OneParameterDerivativeJoint
import OAI.Analysis.SymmetricDomains.ProjectedJetSequencesNot

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
namespace Release061
open Set Filter Topology Metric
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
include hU
omit [LocallyCompactSpace U] in
lemma ambientAut_one_second_fderiv (p : U) :
    fderiv ℂ (fderiv ℂ (1 : Biholomorph U U).ambientAut) p.val=0 := by
  have he : fderiv ℂ (1 : Biholomorph U U).ambientAut =ᶠ[𝓝 p.val]
      (fun _ => (1 : Affine n →L[ℂ] Affine n)) := by
    filter_upwards [hU.mem_nhds p.property] with x hx
    exact derivativeAt_one hU ⟨x,hx⟩
  rw [he.fderiv_eq]
  simp only [fderiv_const_apply]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem firstJet_flow_mul_hasStrictFDerivAt_zero
    (hbd : Bornology.IsBounded U) (p : U)
    (a : ℝ → Biholomorph U U) (ha : Continuous a)
    (ha0 : a 0=1) (ham : ∀ s t, a (s+t)=a s*a t)
    (c : E → Biholomorph U U) (hc0 : c 0=1)
    (L : E →L[ℝ] (Affine n × (Affine n →L[ℂ] Affine n)))
    (hc : HasStrictFDerivAt (fun t => ambientFirstJet p (c t)) L 0)
    (l : E →L[ℝ] ℝ) :
    HasStrictFDerivAt (fun t => ambientFirstJet p (a (l t)*c t))
      (((ContinuousLinearMap.toSpanSingleton ℝ
        (infinitesimalGenerator a p.val,fderiv ℂ (infinitesimalGenerator a) p.val)).comp l)+L) 0 := by
  have hA := oneParameter_joint_hasStrictFDerivAt hU a ha hbd ha0 ham 0 p
  rw [ha0,one_apply,derivativeAt_one hU] at hA
  have hD := oneParameter_derivative_joint_hasStrictFDerivAt hU hbd a ha ha0 ham 0 p
  rw [ha0,one_apply,derivativeAt_one hU,ContinuousLinearMap.one_def,ContinuousLinearMap.comp_id,ambientAut_one_second_fderiv hU] at hD
  have hcval : (c 0).ambientAut p.val=p.val := by rw [hc0,ambientAut_apply,one_apply]
  have hcd : (c 0).derivativeAt p=1 := by rw [hc0,derivativeAt_one hU]
  have hu := l.hasStrictFDerivAt.prodMk hc.fst
  change HasStrictFDerivAt (fun t => (l t,(c t).ambientAut p.val))
    (l.prod ((ContinuousLinearMap.fst ℝ _ _).comp L)) 0 at hu
  have hu0 : (l 0,(c 0).ambientAut p.val)=(0,p.val) := by rw [map_zero,hcval]
  rw [←hu0] at hA hD
  have hAv := hA.comp 0 hu
  have hDv := hD.comp 0 hu
  let B := (ContinuousLinearMap.compL ℂ (Affine n) (Affine n) (Affine n)).bilinearRestrictScalars ℝ
  have hB := (B.isBoundedBilinearMap.hasStrictFDerivAt
    (fderiv ℂ (a (l 0)).ambientAut ((c 0).ambientAut p.val),(c 0).derivativeAt p)).comp 0 (hDv.prodMk hc.snd)
  have hpair := hAv.prodMk hB
  have hfun : (fun t => ambientFirstJet p (a (l t)*c t)) =
      (fun t => ((a (l t)).ambientAut ((c t).ambientAut p.val),
        (fderiv ℂ (a (l t)).ambientAut ((c t).ambientAut p.val)).comp ((c t).derivativeAt p))) := by
    funext t
    apply Prod.ext
    · simp only [ambientFirstJet,ambientAut_apply,mul_apply]
    · simpa only [ambientFirstJet,ambientAut_apply,derivativeAt] using derivativeAt_mul hU (a (l t)) (c t) p
  rw [hfun]
  convert hpair using 1
  · rfl
  apply DFunLike.ext
  intro v
  apply Prod.ext
  · change l v • infinitesimalGenerator a p.val+(L v).1 =
      l v • infinitesimalGenerator a p.val+(L v).1
    rfl
  · change l v • fderiv ℂ (infinitesimalGenerator a) p.val+(L v).2 =
      (fderiv ℂ (a (l 0)).ambientAut ((c 0).ambientAut p.val)).comp ((L v).2) +
      (l v • fderiv ℂ (infinitesimalGenerator a) p.val + (0 : Affine n →L[ℂ] (Affine n →L[ℂ] Affine n)) ((L v).1)).comp ((c 0).derivativeAt p)
    rw [map_zero,ha0,hcval,show fderiv ℂ (1 : Biholomorph U U).ambientAut p.val=1 from derivativeAt_one hU p,hcd]
    simp only [zero_apply,add_zero,ContinuousLinearMap.one_def,ContinuousLinearMap.comp_id,ContinuousLinearMap.id_comp]
    exact add_comm _ _
end Biholomorph
end Release061

end

end OAI
