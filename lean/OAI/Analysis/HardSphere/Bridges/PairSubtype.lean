import Mathlib
import OAI.Analysis.HardSphere.Bridges.PairedMarginal
import OAI.Analysis.HardSphere.Bridges.PhysicalInsertion
import OAI.Analysis.HardSphere.Conditioning.SupportedPair

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison

def pairedPathsRaw (t : ℝ) (y z y' z' : Point) (A : Set Point)
    (S T : Set C(Time,Point)) (hS : MeasurableSet S) (hT : MeasurableSet T) :
    Measure (C(Time,Point)×C(Time,Point)) :=
  (pairedTrialLaw t y z y' z' A S T hS hT).map (fun p ↦ (p.1,p.2.2))

lemma pairedPathsRaw_fst (t : ℝ) (y z y' z' : Point) (A : Set Point)
    (S T : Set C(Time,Point)) (hS : MeasurableSet S) (hT : MeasurableSet T) :
    (pairedPathsRaw t y z y' z' A S T hS hT).fst=(pairedTrialLaw t y z y' z' A S T hS hT).fst := by
  rw [pairedPathsRaw,Measure.fst,Measure.map_map measurable_fst (by fun_prop)]
  rfl
lemma pairedPathsRaw_snd (t : ℝ) (y z y' z' : Point) (A : Set Point)
    (S T : Set C(Time,Point)) (hS : MeasurableSet S) (hT : MeasurableSet T) :
    (pairedPathsRaw t y z y' z' A S T hS hT).snd=(pairedTrialLaw t y z y' z' A S T hS hT).map (fun p ↦ p.2.2) := by
  rw [pairedPathsRaw,Measure.snd,Measure.map_map measurable_snd (by fun_prop)]
  rfl

def pairedPathsOn (t : ℝ) (y z y' z' : Point) (A : Set Point)
    (S T : Set C(Time,Point)) (hS : MeasurableSet S) (hT : MeasurableSet T) : Measure (S×T) :=
  supportedPair (pairedPathsRaw t y z y' z' A S T hS hT) S T

lemma pairedPathsOn_physical {t C C' : ℝ} (ht : 0<t) (hC : 0≤C) (hC' : 0≤C')
    (y z y' z' : Point) {A : Set Point} (hA : MeasurableSet A)
    (hA0 : volume A≠0) (hAfinite : volume A≠⊤)
    (hb : ∀u∈A,‖u-(fun j ↦ (y j+z j)/2)‖≤C)
    (hb' : ∀u∈A,‖u-(fun j ↦ (y' j+z' j)/2)‖≤C')
    (S T : Set C(Time,Point)) (hS : MeasurableSet S) (hT : MeasurableSet T)
    {c d : ℝ≥0∞} (hc0 : 0<c) (hd0 : 0<d)
    (hc : ∀ᵐu ∂targetUniform A,c≤trialKernel t y z u S)
    (hd : ∀ᵐu ∂targetUniform A,d≤trialKernel t y' z' u T) :
    IsProbabilityMeasure (pairedPathsOn t y z y' z' A S T hS hT) ∧
    (pairedPathsOn t y z y' z' A S T hS hT).fst≤
      (c⁻¹*((volume A)⁻¹*(midpointLower t C)⁻¹)) • referenceOn t y z S ∧
    (pairedPathsOn t y z y' z' A S T hS hT).snd≤
      (d⁻¹*((volume A)⁻¹*(midpointLower t C')⁻¹)) • referenceOn t y' z' T ∧
    (∀ᵐp ∂pairedPathsOn t y z y' z' A S T hS hT,
      p.1.val midpointTime=p.2.val midpointTime) := by
  obtain ⟨hP,hQ⟩ := pairedTrialLaw_marginals ht hC hC' y z y' z' hA hA0 hAfinite hb hb' S T hS hT hc0 hd0 hc hd
  rw [←referenceOn_map t y z hS,←pairedPathsRaw_fst t y z y' z' A S T hS hT] at hP
  rw [←referenceOn_map t y' z' hT,←pairedPathsRaw_snd t y z y' z' A S T hS hT] at hQ
  have hρ := supported_of_marginals _ hS hT (referenceOn t y z S) (referenceOn t y' z' T) hP hQ
  let _ : IsProbabilityMeasure (pairedTrialLaw t y z y' z' A S T hS hT) :=
    pairedTrialLaw_probability t y z y' z' A hA0 hAfinite S T hS hT (hc.mono (fun _ hu ↦ hc0.trans_le hu))
      (hd.mono (fun _ hu ↦ hd0.trans_le hu))
  let _ : IsProbabilityMeasure (pairedPathsRaw t y z y' z' A S T hS hT) := by
    unfold pairedPathsRaw
    infer_instance
  refine ⟨supportedPair_probability _ hS hT hρ,supportedPair_fst_le _ hS hT hρ _ hP,
    supportedPair_snd_le _ hS hT hρ _ hQ,?_⟩
  have hm : ∀ᵐp ∂pairedPathsRaw t y z y' z' A S T hS hT,p.1 midpointTime=p.2 midpointTime := by
    apply (ae_map_iff (by fun_prop) (by measurability)).mpr
    exact (pairedTrialLaw_midpoint t y z y' z' A hA0 hAfinite S T hS hT).mono (fun _ hp ↦ hp.1.trans hp.2.symm)
  rw [←supportedPair_map _ hS hT hρ] at hm
  exact (ae_map_iff (by fun_prop) (by measurability)).mp hm

lemma pairedPathsOn_auxiliary {t C C' : ℝ} (ht : 0<t) (hC : 0≤C) (hC' : 0≤C')
    (y z y' z' : Point) {A : Set Point} (hA : MeasurableSet A)
    (hA0 : volume A≠0) (hAfinite : volume A≠⊤)
    (hb : ∀u∈A,‖u-(fun j ↦ (y j+z j)/2)‖≤C)
    (hb' : ∀u∈A,‖u-(fun j ↦ (y' j+z' j)/2)‖≤C')
    (S T : Set C(Time,Point)) (hS : MeasurableSet S) (hT : MeasurableSet T)
    {c d : ℝ≥0∞} (hc0 : 0<c) (hd0 : 0<d)
    (hc : ∀ᵐu ∂targetUniform A,c≤trialKernel t y z u S)
    (hd : ∀ᵐu ∂targetUniform A,d≤trialKernel t y' z' u T) :
    ∃κ : Kernel S T,IsFiniteKernel κ ∧
      (referenceOn t y z S).compProd κ=pairedPathsOn t y z y' z' A S T hS hT ∧
      (∀f,κ f univ≤c⁻¹*((volume A)⁻¹*(midpointLower t C)⁻¹)) ∧
      (∫⁻f,κ f univ ∂referenceOn t y z S)=1 := by
  let _ : IsProbabilityMeasure (referenceOn t y z S) := referenceOn_probability ht hC y z hA hA0 hAfinite hb S hS hc0 hc
  let _ : IsProbabilityMeasure (referenceOn t y' z' T) := referenceOn_probability ht hC' y' z' hA hA0 hAfinite hb' T hT hd0 hd
  let _ : StandardBorelSpace T := hT.standardBorel
  let _ : Nonempty T := nonempty_of_isProbabilityMeasure (referenceOn t y' z' T)
  obtain ⟨hp,hfst,hsnd,hm⟩ := pairedPathsOn_physical ht hC hC' y z y' z' hA hA0 hAfinite hb hb' S T hS hT hc0 hd0 hc hd
  let _ := hp
  exact exists_bounded_auxiliary_kernel _ _
    (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hc0.ne')
      (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hA0) (ENNReal.inv_ne_top.mpr (midpointLower_pos ht C).ne'))) hfst

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison

def pointPathRaw (t : ℝ) (y z : Point) (A : Set Point)
    (S : Set C(Time,Point)) (hS : MeasurableSet S) : Measure (Point×C(Time,Point)) :=
  (targetUniform A).compProd (successKernel (trialKernel t y z) S hS)

lemma pointPathRaw_fst (t : ℝ) (y z : Point) (A : Set Point)
    (hA0 : volume A≠0) (hAf : volume A≠⊤) (S : Set C(Time,Point)) (hS : MeasurableSet S)
    (hc : ∀ᵐu ∂targetUniform A,0<trialKernel t y z u S) :
    (pointPathRaw t y z A S hS).fst=targetUniform A := by
  let _ : IsProbabilityMeasure (targetUniform A) := targetUniform_probability hA0 hAf
  ext B hB
  rw [Measure.fst,Measure.map_apply measurable_fst hB,pointPathRaw,Measure.compProd_apply (hB.preimage measurable_fst)]
  have he : (fun u ↦ successKernel (trialKernel t y z) S hS u ((fun v ↦ (u,v))⁻¹' (Prod.fst ⁻¹' B)))
      =ᵐ[targetUniform A] B.indicator (fun _ ↦ (1:ℝ≥0∞)) := by
    filter_upwards [hc] with u hu
    by_cases h : u∈B
    · simp only [Set.preimage_preimage]
      have hh : {v : C(Time,Point) | (u,v).1∈B}=univ := by ext v; simp [h]
      change successKernel (trialKernel t y z) S hS u {v | (u,v).1∈B}=_
      rw [hh,successKernel_mass _ _ _ hu,Set.indicator_of_mem h]
    · have hh : (fun v : C(Time,Point) ↦ (u,v))⁻¹' (Prod.fst ⁻¹' B)=∅ := by ext v; simp [h]
      rw [hh,measure_empty,Set.indicator_of_notMem h]
  rw [lintegral_congr_ae he,lintegral_indicator hB]
  simp

lemma pointPathRaw_probability (t : ℝ) (y z : Point) (A : Set Point)
    (hA0 : volume A≠0) (hAf : volume A≠⊤) (S : Set C(Time,Point)) (hS : MeasurableSet S)
    (hc : ∀ᵐu ∂targetUniform A,0<trialKernel t y z u S) :
    IsProbabilityMeasure (pointPathRaw t y z A S hS) := by
  let _ : IsProbabilityMeasure (targetUniform A) := targetUniform_probability hA0 hAf
  constructor
  have h := congrArg (fun μ : Measure Point ↦ μ univ) (pointPathRaw_fst t y z A hA0 hAf S hS hc)
  simpa only [Measure.fst,Measure.map_apply measurable_fst MeasurableSet.univ,preimage_univ,measure_univ] using h

lemma pointPathRaw_midpoint (t : ℝ) (y z : Point) (A : Set Point)
    (hA0 : volume A≠0) (hAf : volume A≠⊤) (S : Set C(Time,Point)) (hS : MeasurableSet S) :
    ∀ᵐp ∂pointPathRaw t y z A S hS,p.2 midpointTime=p.1 := by
  let _ : IsProbabilityMeasure (targetUniform A) := targetUniform_probability hA0 hAf
  unfold pointPathRaw
  apply Measure.ae_compProd_of_ae_ae (by measurability)
  exact ae_of_all _ (fun u ↦ (successKernel_absolutelyContinuous (trialKernel t y z) S hS u).ae_le
    (trialKernel_midpoint t y z u))

lemma targetUniform_le_cell {A B : Set Point} (hAB : A⊆B) (hB : volume B=1) :
    targetUniform A≤(volume A)⁻¹ • targetUniform B := by
  simp only [targetUniform,hB,inv_one,one_smul]
  intro E
  simp only [Measure.smul_apply,smul_eq_mul]
  exact mul_le_mul' le_rfl (Measure.restrict_mono hAB (μ:=volume) le_rfl E)

def pointPathOn (t : ℝ) (y z : Point) (A B : Set Point)
    (S : Set C(Time,Point)) (hS : MeasurableSet S) : Measure (B×S) :=
  supportedPair (pointPathRaw t y z A S hS) B S

lemma pointPathOn_physical {t C : ℝ} (ht : 0<t) (hC : 0≤C) (y z : Point)
    {A B : Set Point} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hA0 : volume A≠0) (hAf : volume A≠⊤) (hBvol : volume B=1) (hAB : A⊆B)
    (hb : ∀u∈A,‖u-(fun j ↦ (y j+z j)/2)‖≤C)
    (S : Set C(Time,Point)) (hS : MeasurableSet S) {c : ℝ≥0∞} (hc0 : 0<c)
    (hc : ∀ᵐu ∂targetUniform A,c≤trialKernel t y z u S) :
    IsProbabilityMeasure (pointPathOn t y z A B S hS) ∧
    (pointPathOn t y z A B S hS).fst≤(volume A)⁻¹ • subtypeConditional volume B ∧
    (pointPathOn t y z A B S hS).snd≤
      (c⁻¹*((volume A)⁻¹*(midpointLower t C)⁻¹)) • referenceOn t y z S ∧
    (∀ᵐp ∂pointPathOn t y z A B S hS,p.2.val midpointTime=p.1.val) := by
  have hp := hc.mono (fun _ h ↦ hc0.trans_le h)
  have hfst : (pointPathRaw t y z A S hS).fst≤(volume A)⁻¹ • (subtypeConditional volume B).map Subtype.val := by
    rw [pointPathRaw_fst t y z A hA0 hAf S hS hp,subtypeConditional_map volume hB]
    exact targetUniform_le_cell hAB hBvol
  have hsnd : (pointPathRaw t y z A S hS).snd≤
      (c⁻¹*((volume A)⁻¹*(midpointLower t C)⁻¹)) • (referenceOn t y z S).map Subtype.val := by
    rw [referenceOn_map t y z hS]
    exact physical_trial_le_reference ht hC y z hA hAf hb S hS hc
  have hs := supported_of_marginals _ hB hS (subtypeConditional volume B) (referenceOn t y z S) hfst hsnd
  let _ := pointPathRaw_probability t y z A hA0 hAf S hS hp
  refine ⟨supportedPair_probability _ hB hS hs,supportedPair_fst_le _ hB hS hs _ hfst,
    supportedPair_snd_le _ hB hS hs _ hsnd,?_⟩
  have hm := pointPathRaw_midpoint t y z A hA0 hAf S hS
  rw [←supportedPair_map _ hB hS hs] at hm
  exact (ae_map_iff (by fun_prop) (by measurability)).mp hm

end HardSphere.Bridge

end
end

end

end OAI
