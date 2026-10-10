import Mathlib
import OAI.Analysis.HardSphere.Kernels.ParameterSuccess
import OAI.Analysis.HardSphere.Kernels.TrialObserved
import OAI.Analysis.HardSphere.Bridges.BridgeReference
import OAI.Analysis.HardSphere.Kernels.KernelDensity

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison

def targetUniform (A : Set Point) : Measure Point := (volume A)⁻¹ • volume.restrict A
lemma targetUniform_probability {A : Set Point} (hA0 : volume A≠0) (hAfinite : volume A≠⊤) : IsProbabilityMeasure (targetUniform A) := by
  constructor
  simp only [targetUniform,Measure.smul_apply,Measure.restrict_apply_univ,smul_eq_mul]
  exact ENNReal.inv_mul_cancel hA0 hAfinite

def midpointLower (t C : ℝ) : ℝ≥0∞ := ENNReal.ofReal (densityLower ((2*t)⁻¹) C)
lemma midpointLower_pos {t : ℝ} (ht : 0<t) (C : ℝ) : 0 < midpointLower t C :=
  ENNReal.ofReal_pos.mpr (densityLower_pos (by positivity) C)
lemma midpointLower_ne_top (t C : ℝ) : midpointLower t C≠⊤ := ENNReal.ofReal_ne_top

lemma targetUniform_le_midpoint {t C : ℝ} (ht : 0<t) (hC : 0≤C) (y z : Point)
    {A : Set Point} (hA : MeasurableSet A) (hbound : ∀x∈A,‖x-(fun j ↦ (y j+z j)/2)‖≤C) :
    targetUniform A≤((volume A)⁻¹*(midpointLower t C)⁻¹) • midpointLaw t y z := by
  have h := gaussian_dominates_local (v:=Real.toNNReal t) (by simpa [Real.toNNReal_eq_zero] using not_le.mpr ht)
    (fun j ↦ (y j+z j)/2) hC hA hbound
  rw [←midpointLaw_gaussian ht.le y z,Real.coe_toNNReal t ht.le] at h
  change midpointLower t C • volume.restrict A ≤ midpointLaw t y z at h
  have hd0 := ne_of_gt (midpointLower_pos ht C)
  intro B
  have hh := mul_le_mul_right (h B) ((volume A)⁻¹*(midpointLower t C)⁻¹)
  have he : (volume A)⁻¹*(midpointLower t C)⁻¹*midpointLower t C=(volume A)⁻¹ := by
    rw [mul_assoc,ENNReal.inv_mul_cancel hd0 (midpointLower_ne_top t C),mul_one]
  simpa only [targetUniform,Measure.smul_apply,smul_eq_mul,←mul_assoc,he] using hh

def individualReference (t : ℝ) (y z : Point) (S : Set C(Time,Point)) : Measure C(Time,Point) :=
  ((law.map (leg (2*t) y z)) S)⁻¹ • (law.map (leg (2*t) y z)).restrict S

lemma physical_trial_le_reference {t C : ℝ} (ht : 0<t) (hC : 0≤C) (y z : Point)
    {A : Set Point} (hA : MeasurableSet A) (hAfinite : volume A≠⊤)
    (hbound : ∀x∈A,‖x-(fun j ↦ (y j+z j)/2)‖≤C)
    (S : Set C(Time,Point)) (hS : MeasurableSet S) {c : ℝ≥0∞}
    (hc : ∀ᵐu ∂targetUniform A,c≤trialKernel t y z u S) :
    ((targetUniform A).compProd (successKernel (trialKernel t y z) S hS)).map Prod.snd ≤
      (c⁻¹*((volume A)⁻¹*(midpointLower t C)⁻¹)) • individualReference t y z S := by
  let : IsFiniteMeasure (volume.restrict A) := ⟨by simp [hAfinite.lt_top]⟩
  let : IsFiniteMeasure (targetUniform A) := by
    by_cases h0 : volume A=0
    · have hz : targetUniform A=0 := by simp [targetUniform,Measure.restrict_eq_zero.mpr h0]
      rw [hz]
      infer_instance
    · let : IsProbabilityMeasure (targetUniform A) := targetUniform_probability h0 hAfinite
      infer_instance
  have h := successful_marginal_le_reference (targetUniform A) (midpointLaw t y z)
    (trialKernel t y z) S hS (targetUniform_le_midpoint ht hC y z hA hbound) hc
  simpa only [full_bridge_midpoint ht.le,individualReference] using h

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison

lemma individualReference_probability {t C : ℝ} (ht : 0<t) (hC : 0≤C) (y z : Point)
    {A : Set Point} (hA : MeasurableSet A) (hA0 : volume A≠0) (hAfinite : volume A≠⊤)
    (hbound : ∀u∈A,‖u-(fun j ↦ (y j+z j)/2)‖≤C)
    (S : Set C(Time,Point)) (hS : MeasurableSet S) {c : ℝ≥0∞} (hc0 : 0<c)
    (hc : ∀ᵐu ∂targetUniform A,c≤trialKernel t y z u S) :
    IsProbabilityMeasure (individualReference t y z S) := by
  let _ : IsProbabilityMeasure (targetUniform A) := targetUniform_probability hA0 hAfinite
  have hp := normalizer_positive_of_uniform_success (targetUniform A) (midpointLaw t y z)
    (trialKernel t y z) S hS hc0 (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hA0)
      (ENNReal.inv_ne_top.mpr (midpointLower_pos ht C).ne'))
    (targetUniform_le_midpoint ht hC y z hA hbound) hc
  rw [full_bridge_midpoint ht.le y z] at hp
  let _ : IsProbabilityMeasure (law.map (leg (2*t) y z)) := inferInstance
  constructor
  simp only [individualReference,Measure.smul_apply,Measure.restrict_apply_univ,smul_eq_mul]
  exact ENNReal.inv_mul_cancel hp.ne' (measure_ne_top _ _)

def pairedTrialLaw (t : ℝ) (y z y' z' : Point) (A : Set Point)
    (S T : Set C(Time,Point)) (hS : MeasurableSet S) (hT : MeasurableSet T) :
    Measure (C(Time,Point)×(Point×C(Time,Point))) :=
  (pairedFactor (targetUniform A) (trialKernel t y z) (trialKernel t y' z') S T hS hT).map
    (fun p ↦ (p.2.1,(p.1,p.2.2)))

lemma pairedTrialLaw_probability (t : ℝ) (y z y' z' : Point) (A : Set Point)
    (hA0 : volume A≠0) (hAfinite : volume A≠⊤)
    (S T : Set C(Time,Point)) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hκ : ∀ᵐu ∂targetUniform A,0<trialKernel t y z u S)
    (hη : ∀ᵐu ∂targetUniform A,0<trialKernel t y' z' u T) :
    IsProbabilityMeasure (pairedTrialLaw t y z y' z' A S T hS hT) := by
  let _ : IsProbabilityMeasure (targetUniform A) := targetUniform_probability hA0 hAfinite
  let _ : IsProbabilityMeasure (pairedFactor (targetUniform A) (trialKernel t y z) (trialKernel t y' z') S T hS hT) :=
    ⟨pairedFactor_mass _ _ _ _ _ _ _ hκ hη⟩
  unfold pairedTrialLaw
  infer_instance

lemma pairedTrialLaw_fst (t : ℝ) (y z y' z' : Point) (A : Set Point)
    (hA0 : volume A≠0) (hAfinite : volume A≠⊤)
    (S T : Set C(Time,Point)) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hη : ∀ᵐu ∂targetUniform A,0<trialKernel t y' z' u T) :
    (pairedTrialLaw t y z y' z' A S T hS hT).fst=
      ((targetUniform A).compProd (successKernel (trialKernel t y z) S hS)).map Prod.snd := by
  let _ : IsProbabilityMeasure (targetUniform A) := targetUniform_probability hA0 hAfinite
  have h := congrArg (fun μ : Measure (Point×C(Time,Point)) ↦ μ.map Prod.snd)
    (pairedFactor_fst (targetUniform A) (trialKernel t y z) (trialKernel t y' z') S T hS hT hη)
  rw [Measure.map_map measurable_snd (by fun_prop)] at h
  unfold pairedTrialLaw Measure.fst
  rw [Measure.map_map measurable_fst (by fun_prop)]
  exact h

lemma pairedTrialLaw_midpoint (t : ℝ) (y z y' z' : Point) (A : Set Point)
    (hA0 : volume A≠0) (hAfinite : volume A≠⊤)
    (S T : Set C(Time,Point)) (hS : MeasurableSet S) (hT : MeasurableSet T) :
    ∀ᵐp ∂pairedTrialLaw t y z y' z' A S T hS hT,
      p.1 midpointTime=p.2.1 ∧ p.2.2 midpointTime=p.2.1 := by
  let _ : IsProbabilityMeasure (targetUniform A) := targetUniform_probability hA0 hAfinite
  rw [pairedTrialLaw]
  apply (ae_map_iff (by fun_prop) (by measurability)).mpr
  exact paired_trial_midpoint (targetUniform A) t y z y' z' S T hS hT

lemma pairedTrial_auxiliary {t C : ℝ} (ht : 0<t) (hC : 0≤C) (y z y' z' : Point)
    {A : Set Point} (hA : MeasurableSet A) (hA0 : volume A≠0) (hAfinite : volume A≠⊤)
    (hbound : ∀u∈A,‖u-(fun j ↦ (y j+z j)/2)‖≤C)
    (S T : Set C(Time,Point)) (hS : MeasurableSet S) (hT : MeasurableSet T)
    {c : ℝ≥0∞} (hc0 : 0<c) (hc : ∀ᵐu ∂targetUniform A,c≤trialKernel t y z u S)
    (hη : ∀ᵐu ∂targetUniform A,0<trialKernel t y' z' u T) :
    ∃ κ : Kernel C(Time,Point) (Point×C(Time,Point)),IsFiniteKernel κ ∧
      (individualReference t y z S).compProd κ=pairedTrialLaw t y z y' z' A S T hS hT ∧
      (∀f,κ f univ≤c⁻¹*((volume A)⁻¹*(midpointLower t C)⁻¹)) ∧
      (∫⁻f,κ f univ ∂individualReference t y z S)=1 := by
  let _ : IsProbabilityMeasure (individualReference t y z S) :=
    individualReference_probability ht hC y z hA hA0 hAfinite hbound S hS hc0 hc
  let _ : IsProbabilityMeasure (pairedTrialLaw t y z y' z' A S T hS hT) :=
    pairedTrialLaw_probability t y z y' z' A hA0 hAfinite S T hS hT (hc.mono (fun _ hu ↦ hc0.trans_le hu)) hη
  apply exists_bounded_auxiliary_kernel
  · exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hc0.ne')
      (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hA0) (ENNReal.inv_ne_top.mpr (midpointLower_pos ht C).ne'))
  · rw [pairedTrialLaw_fst t y z y' z' A hA0 hAfinite S T hS hT hη]
    exact physical_trial_le_reference ht hC y z hA hAfinite hbound S hS hc

end HardSphere.Bridge

end
end

end

end OAI
