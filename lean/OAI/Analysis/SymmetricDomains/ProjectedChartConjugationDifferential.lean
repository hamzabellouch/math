import Mathlib
import OAI.Analysis.SymmetricDomains.FirstJetConstMul

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

theorem oneParameter_firstJet_hasDerivAt_zero (hbd : Bornology.IsBounded U)
    (a : ℝ → Biholomorph U U) (ha : Continuous a)
    (ha0 : a 0=1) (ham : ∀ s t, a (s+t)=a s*a t) (p : U) :
    HasDerivAt (fun t => ambientFirstJet p (a t))
      (infinitesimalGenerator a p.val, fderiv ℂ (infinitesimalGenerator a) p.val) 0 := by
  have hv := oneParameter_hasDerivAt_zero hU a ha hbd ha0 ham p
  have hd := oneParameter_fderiv_hasDerivAt_zero hU hbd a ha ha0 ham p.val p.property
  simpa only [ambientFirstJet,ambientAut_apply,derivativeAt] using hv.prodMk hd

variable (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) (p : U)
include hU hc hbd Γ hhol

theorem projected_chart_conjugation_differential
    (P : (Affine n × (Affine n →L[ℂ] Affine n)) →L[ℝ]
        LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p))
    (e : OpenPartialHomeomorph (Biholomorph U U)
        (LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p)))
    (he : (e : Biholomorph U U → _)=(fun a => P (ambientFirstJet p a)))
    (he1 : 1∈e.source)
    (hreg : ∀ p' : U, ∃ L : LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p) →L[ℝ]
        (Affine n × (Affine n →L[ℂ] Affine n)),
      HasStrictFDerivAt (𝕜 := ℝ) (E := LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p))
        (F := Affine n × (Affine n →L[ℂ] Affine n)) (fun t => ambientFirstJet p' (e.symm t)) L (e 1))
    (g : Biholomorph U U) :
    ∃ L : LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p) →L[ℝ]
        LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p),
      HasStrictFDerivAt (𝕜 := ℝ) (fun t => e (g*e.symm t*g⁻¹)) L (e 1) ∧
      ∀ X : completeGeneratorSpace hU hc hbd Γ hhol,
        L (P (completeGeneratorFirstJet hU hc hbd Γ hhol p X))=
          P (completeGeneratorFirstJet hU hc hbd Γ hhol p (generatorAdjoint hU hc hbd Γ hhol g X)) := by
  let J := completeGeneratorFirstJet hU hc hbd Γ hhol p
  let R : Type := J.range
  let _ : NormedAddCommGroup R := Submodule.normedAddCommGroup _
  let _ : NormedSpace ℝ R := Submodule.normedSpace _
  obtain ⟨L0,hL0⟩ := hreg (g⁻¹.toHomeomorph p)
  obtain ⟨L1,hL1⟩ := exists_firstJet_mul_const_strictFDeriv (E := R) hU p g⁻¹ e.symm (e 1) L0 hL0
  obtain ⟨L2,hL2⟩ := exists_firstJet_const_mul_strictFDeriv (E := R) hU p g
    (fun t => e.symm t*g⁻¹) (e 1) L1 hL1
  have hPc := ContinuousLinearMap.hasStrictFDerivAt (𝕜 := ℝ)
    (E := Affine n × (Affine n →L[ℂ] Affine n)) (F := R)
    (x := ambientFirstJet p (g*(e.symm (e 1)*g⁻¹))) P
  have hproj := HasStrictFDerivAt.comp (𝕜 := ℝ) (E := R)
    (F := Affine n × (Affine n →L[ℂ] Affine n)) (G := R) (e 1) hPc hL2
  have hL : HasStrictFDerivAt (fun t => e (g*e.symm t*g⁻¹)) (P.comp L2) (e 1) := by
    simpa only [he,mul_assoc] using hproj
  refine ⟨P.comp L2,hL,?_⟩
  intro X
  obtain ⟨a,ha,ha0,ham,hgen⟩ := X.property
  have hja : HasDerivAt (fun s => ambientFirstJet p (a s)) (J X) 0 := by
    have hh := oneParameter_firstJet_hasDerivAt_zero hU hbd a ha ha0 ham p
    rw [hgen] at hh
    exact hh
  have hpa : HasDerivAt (fun s => e (a s)) (P (J X)) 0 := by
    have hp := (ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ)
      (E := Affine n × (Affine n →L[ℂ] Affine n)) (F := R)
      (x := ambientFirstJet p (a 0)) P).comp_hasDerivAt 0 hja
    simpa only [Function.comp_def,he] using hp
  have hL' : HasFDerivAt (fun t : R => e (g*e.symm t*g⁻¹)) (P.comp L2) (e (a 0)) := by
    simpa only [ha0] using hL.hasFDerivAt
  have hchain := hL'.comp_hasDerivAt (0:ℝ) hpa
  have hasrc : ∀ᶠ s in 𝓝 (0:ℝ), a s∈e.source := by
    have ht : Tendsto a (𝓝 0) (𝓝 (1 : Biholomorph U U)) := by simpa only [ha0] using ha.continuousAt.tendsto (x := 0)
    exact ht (e.open_source.mem_nhds he1)
  have hconj : HasDerivAt (fun s => e (g*a s*g⁻¹)) ((P.comp L2) (P (J X))) 0 := by
    apply hchain.congr_of_eventuallyEq
    filter_upwards [hasrc] with s hs
    simp only [Function.comp_def,e.left_inv hs]
  have hca : Continuous (fun s => g*a s*g⁻¹) := (continuous_const.mul ha).mul continuous_const
  have hca0 : g*a 0*g⁻¹=1 := by simp only [ha0,mul_one,mul_inv_cancel]
  have hcam : ∀ s t, g*a (s+t)*g⁻¹=(g*a s*g⁻¹)*(g*a t*g⁻¹) := by
    intro s t
    rw [ham]
    group
  have hcj := oneParameter_firstJet_hasDerivAt_zero hU hbd (fun s => g*a s*g⁻¹) hca hca0 hcam p
  rw [infinitesimalGenerator_conjugate hU hbd a ha ha0 ham g,hgen] at hcj
  have hcj' : HasDerivAt (fun s => ambientFirstJet p (g*a s*g⁻¹))
      (J (generatorAdjoint hU hc hbd Γ hhol g X)) 0 := hcj
  have hpj := (ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ)
      (E := Affine n × (Affine n →L[ℂ] Affine n)) (F := R)
      (x := ambientFirstJet p (g*a 0*g⁻¹)) P).comp_hasDerivAt 0 hcj'
  have hpj' : HasDerivAt (fun s => e (g*a s*g⁻¹))
      (P (J (generatorAdjoint hU hc hbd Γ hhol g X))) 0 := by simpa only [Function.comp_def,he] using hpj
  exact hconj.unique hpj'
end Biholomorph
end Release061

end

end OAI
