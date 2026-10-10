import Mathlib
import OAI.Analysis.SymmetricDomains.FirstJetFlowMul

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

section
variable {n : ℕ} {U : Set (Affine n)} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*}

def flowWord (a : ι → ℝ → Biholomorph U U) (l : ι → E →L[ℝ] ℝ) :
    List ι → E → Biholomorph U U
  | [],_ => 1
  | i::is,t => a i (l i t)*flowWord a l is t

theorem flowWord_zero (a : ι → ℝ → Biholomorph U U) (l : ι → E →L[ℝ] ℝ)
    (ha0 : ∀ i, a i 0=1) (is : List ι) : flowWord a l is 0=1 := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [flowWord,map_zero,ha0,ih,mul_one]

theorem flowWord_continuous [LocallyCompactSpace U]
    (a : ι → ℝ → Biholomorph U U) (l : ι → E →L[ℝ] ℝ)
    (ha : ∀ i, Continuous (a i)) (is : List ι) : Continuous (flowWord a l is) := by
  induction is with
  | nil => exact continuous_const
  | cons i is ih => exact ((ha i).comp (l i).continuous).mul ih

theorem flowWord_firstJet_hasStrictFDerivAt_zero
    (hU : IsOpen U) [LocallyCompactSpace U] (hbd : Bornology.IsBounded U) (p : U)
    (a : ι → ℝ → Biholomorph U U) (l : ι → E →L[ℝ] ℝ)
    (ha : ∀ i, Continuous (a i)) (ha0 : ∀ i, a i 0=1)
    (ham : ∀ i s t, a i (s+t)=a i s*a i t) (is : List ι) :
    HasStrictFDerivAt (fun t => ambientFirstJet p (flowWord a l is t))
      ((is.map (fun i => (ContinuousLinearMap.toSpanSingleton ℝ
        (infinitesimalGenerator (a i) p.val,fderiv ℂ (infinitesimalGenerator (a i)) p.val)).comp (l i))).sum) 0 := by
  induction is with
  | nil =>
    change HasStrictFDerivAt (fun _ : E => ambientFirstJet p (1 : Biholomorph U U)) 0 0
    exact hasStrictFDerivAt_const _ _
  | cons i is ih =>
    exact firstJet_flow_mul_hasStrictFDerivAt_zero hU hbd p (a i) (ha i) (ha0 i) (ham i)
      (flowWord a l is) (flowWord_zero a l ha0 is) _ ih (l i)
end

variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
include hU
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_firstJet_flow_mul_strictFDeriv
    (hbd : Bornology.IsBounded U) (p : U)
    (a : ℝ → Biholomorph U U) (ha : Continuous a)
    (ha0 : a 0=1) (ham : ∀ s t, a (s+t)=a s*a t)
    (c : E → Biholomorph U U) (t₀ : E)
    (L : E →L[ℝ] (Affine n × (Affine n →L[ℂ] Affine n)))
    (hc : HasStrictFDerivAt (fun t => ambientFirstJet p (c t)) L t₀)
    (l : E →L[ℝ] ℝ) :
    ∃ L' : E →L[ℝ] (Affine n × (Affine n →L[ℂ] Affine n)),
      HasStrictFDerivAt (fun t => ambientFirstJet p (a (l t)*c t)) L' t₀ := by
  have hA := oneParameter_joint_hasStrictFDerivAt hU a ha hbd ha0 ham (l t₀) ((c t₀).toHomeomorph p)
  have hD := oneParameter_derivative_joint_hasStrictFDerivAt hU hbd a ha ha0 ham (l t₀) ((c t₀).toHomeomorph p)
  have hu := l.hasStrictFDerivAt.prodMk hc.fst
  change HasStrictFDerivAt (fun t => (l t,(c t).ambientAut p.val))
    (l.prod ((ContinuousLinearMap.fst ℝ _ _).comp L)) t₀ at hu
  have hu0 : (l t₀,(c t₀).ambientAut p.val)=(l t₀,((c t₀).toHomeomorph p).val) := by rw [ambientAut_apply]
  rw [←hu0] at hA hD
  have hAv := hA.comp t₀ hu
  have hDv := hD.comp t₀ hu
  let B := (ContinuousLinearMap.compL ℂ (Affine n) (Affine n) (Affine n)).bilinearRestrictScalars ℝ
  have hB := (B.isBoundedBilinearMap.hasStrictFDerivAt
    (fderiv ℂ (a (l t₀)).ambientAut ((c t₀).ambientAut p.val),(c t₀).derivativeAt p)).comp t₀ (hDv.prodMk hc.snd)
  have hpair := hAv.prodMk hB
  have hfun : (fun t => ambientFirstJet p (a (l t)*c t)) =
      (fun t => ((a (l t)).ambientAut ((c t).ambientAut p.val),
        (fderiv ℂ (a (l t)).ambientAut ((c t).ambientAut p.val)).comp ((c t).derivativeAt p))) := by
    funext t
    apply Prod.ext
    · simp only [ambientFirstJet,ambientAut_apply,mul_apply]
    · simpa only [ambientFirstJet,ambientAut_apply,derivativeAt] using derivativeAt_mul hU (a (l t)) (c t) p
  rw [hfun]
  exact ⟨_,hpair⟩

theorem flowWord_exists_firstJet_strictFDeriv {ι : Type*}
    (hbd : Bornology.IsBounded U) (p : U)
    (a : ι → ℝ → Biholomorph U U) (l : ι → E →L[ℝ] ℝ)
    (ha : ∀ i, Continuous (a i)) (ha0 : ∀ i, a i 0=1)
    (ham : ∀ i s t, a i (s+t)=a i s*a i t) (is : List ι) (t₀ : E) :
    ∃ L : E →L[ℝ] (Affine n × (Affine n →L[ℂ] Affine n)),
      HasStrictFDerivAt (fun t => ambientFirstJet p (flowWord a l is t)) L t₀ := by
  induction is with
  | nil =>
    refine ⟨0,?_⟩
    change HasStrictFDerivAt (fun _ : E => ambientFirstJet p (1 : Biholomorph U U)) 0 t₀
    exact hasStrictFDerivAt_const _ _
  | cons i is ih =>
    obtain ⟨L,hL⟩ := ih
    exact exists_firstJet_flow_mul_strictFDeriv hU hbd p (a i) (ha i) (ha0 i) (ham i)
      (flowWord a l is) t₀ L hL (l i)
end Biholomorph
end Release061

end

end OAI
