import Mathlib
import OAI.Analysis.BiholderTransport.Contact.MiddleExclusion
import OAI.Analysis.BiholderTransport.CostGeometry.OuterCurvature

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace WeakMTWTransport

lemma centerTemplate_deriv_polynomial (s:ℝ) :
    deriv centerTemplate s= -(centerGamma/2)*(1-(centerTemplate s)^2) := by
  rw [(hasDerivAt_centerTemplate s).deriv]
  unfold centerTemplate
  have hd : 1+Real.exp (-centerGamma*(s-5/8)) ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

lemma centerTemplate_second (s:ℝ) :
    iteratedDeriv 2 centerTemplate s=centerGamma*centerTemplate s*deriv centerTemplate s := by
  have H : deriv centerTemplate=(fun s=> -(centerGamma/2)*(1-(centerTemplate s)^2)) :=
    funext centerTemplate_deriv_polynomial
  have HD:=(((hasDerivAt_centerTemplate s).pow 2).const_sub 1).const_mul (-(centerGamma/2))
  have HD' : HasDerivAt (fun x=> -(centerGamma/2)*(1-(centerTemplate x)^2))
      (centerGamma*centerTemplate s*deriv centerTemplate s) s := by
    convert! HD using 1
    rw [(hasDerivAt_centerTemplate s).deriv]
    norm_num
    ring
  simp only [iteratedDeriv_succ,iteratedDeriv_zero]
  calc
    deriv (deriv centerTemplate) s = deriv (fun x=> -(centerGamma/2)*(1-(centerTemplate x)^2)) s :=
      congrArg (fun f=>deriv f s) H
    _ = _ := HD'.deriv

lemma centerTemplate_deriv_bound (s:ℝ) :
    0 < -deriv centerTemplate s ∧ -deriv centerTemplate s ≤ centerGamma/2 := by
  refine ⟨neg_pos.mpr (centerTemplate_deriv_neg s),?_⟩
  rw [centerTemplate_deriv_polynomial]
  nlinarith only [centerGamma_pos,sq_nonneg (centerTemplate s)]

lemma centerTemplate_curvature {s:ℝ} (hs:0 < centerTemplate s) :
    iteratedDeriv 2 centerTemplate s < 0 ∧
    -iteratedDeriv 2 centerTemplate s ≤ centerGamma*(-deriv centerTemplate s) ∧
    -iteratedDeriv 2 centerTemplate s ≤ centerGamma^2/2 := by
  rw [centerTemplate_second]
  have hd:=centerTemplate_deriv_neg s
  have hb:=(centerTemplate_bounds s).2
  have hu:=(centerTemplate_deriv_bound s).2
  have H : -(centerGamma*centerTemplate s*deriv centerTemplate s) ≤
      centerGamma*(-deriv centerTemplate s) := by
    nlinarith only [mul_nonneg centerGamma_pos.le (neg_nonneg.mpr hd.le),hb]
  refine ⟨mul_neg_of_pos_of_neg (mul_pos centerGamma_pos hs) hd,H,?_⟩
  nlinarith only [H,mul_le_mul_of_nonneg_left hu centerGamma_pos.le]

lemma outerTemplate_eq_profile (M K eta:ℝ) : outerTemplate M K eta=outerProfile K M eta := by
  funext s
  simp only [outerTemplate,outerPrimitive,outerProfile,outerJ,templateEps_eq]
  congr 2
  norm_num

lemma exact_outer_curvature {M K eta s:ℝ} (hK:1 ≤ K) (hM:2 ≤ M) (heta:0 < eta)
    (hs:-2*eta ≤ s) (hs':s ≤ 1-eta) (hcap:outerTemplate M K eta s ≤ M) :
    0 < deriv (outerTemplate M K eta) s ∧
    iteratedDeriv 2 (outerTemplate M K eta) s ≤ -K := by
  rw [outerTemplate_eq_profile] at hcap ⊢
  exact outerProfile_curvature hK hM heta hs hs' hcap

end WeakMTWTransport

end

end OAI
