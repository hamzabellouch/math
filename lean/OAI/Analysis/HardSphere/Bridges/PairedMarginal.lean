import Mathlib
import OAI.Analysis.HardSphere.Bridges.PhysicalSuccess
import OAI.Analysis.HardSphere.Bridges.LocalReference

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff Comparison

lemma pairedTrialLaw_other (t : ℝ) (y z y' z' : Point) (A : Set Point)
    (hA0 : volume A≠0) (hAfinite : volume A≠⊤)
    (S T : Set C(Time,Point)) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hκ : ∀ᵐu ∂targetUniform A,0<trialKernel t y z u S) :
    (pairedTrialLaw t y z y' z' A S T hS hT).map (fun p ↦ p.2.2)=
      ((targetUniform A).compProd (successKernel (trialKernel t y' z') T hT)).map Prod.snd := by
  let _ : IsProbabilityMeasure (targetUniform A) := targetUniform_probability hA0 hAfinite
  have h := congrArg (fun μ : Measure (Point×C(Time,Point)) ↦ μ.map Prod.snd)
    (pairedFactor_snd (targetUniform A) (trialKernel t y z) (trialKernel t y' z') S T hS hT hκ)
  rw [Measure.map_map measurable_snd (by fun_prop)] at h
  unfold pairedTrialLaw
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  exact h

lemma pairedTrialLaw_marginals {t C C' : ℝ} (ht : 0<t) (hC : 0≤C) (hC' : 0≤C')
    (y z y' z' : Point) {A : Set Point} (hA : MeasurableSet A)
    (hA0 : volume A≠0) (hAfinite : volume A≠⊤)
    (hb : ∀u∈A,‖u-(fun j ↦ (y j+z j)/2)‖≤C)
    (hb' : ∀u∈A,‖u-(fun j ↦ (y' j+z' j)/2)‖≤C')
    (S T : Set C(Time,Point)) (hS : MeasurableSet S) (hT : MeasurableSet T)
    {c d : ℝ≥0∞} (hc0 : 0<c) (hd0 : 0<d)
    (hc : ∀ᵐu ∂targetUniform A,c≤trialKernel t y z u S)
    (hd : ∀ᵐu ∂targetUniform A,d≤trialKernel t y' z' u T) :
    (pairedTrialLaw t y z y' z' A S T hS hT).fst≤
      (c⁻¹*((volume A)⁻¹*(midpointLower t C)⁻¹)) • individualReference t y z S ∧
    (pairedTrialLaw t y z y' z' A S T hS hT).map (fun p ↦ p.2.2)≤
      (d⁻¹*((volume A)⁻¹*(midpointLower t C')⁻¹)) • individualReference t y' z' T := by
  constructor
  · rw [pairedTrialLaw_fst t y z y' z' A hA0 hAfinite S T hS hT (hd.mono (fun _ h ↦ hd0.trans_le h))]
    exact physical_trial_le_reference ht hC y z hA hAfinite hb S hS hc
  · rw [pairedTrialLaw_other t y z y' z' A hA0 hAfinite S T hS hT (hc.mono (fun _ h ↦ hc0.trans_le h))]
    exact physical_trial_le_reference ht hC' y' z' hA hAfinite hb' T hT hd

lemma measure_collision_marginals {L : Length}
    (ρ : Measure (C(Time,Point)×(Point×C(Time,Point))))
    (P Q : Measure C(Time,Point)) {G H p q : ℝ≥0∞}
    (hP : ρ.fst≤G • P) (hQ : ρ.map (fun p ↦ p.2.2)≤H • Q)
    (r : ℝ) (ω ω' : ConfigurationPath 1 L)
    (hp : P {f | TrialCollision r ω f}≤p) (hq : Q {f | TrialCollision r ω' f}≤q) :
    ρ {f | TrialCollision r ω f.1 ∨ TrialCollision r ω' f.2.2}≤G*p+H*q := by
  have h₁ : MeasurableSet {f : C(Time,Point) | TrialCollision r ω f} := (trialCollision_closed r ω).measurableSet
  have h₂ : MeasurableSet {f : C(Time,Point) | TrialCollision r ω' f} := (trialCollision_closed r ω').measurableSet
  calc
    _ ≤ ρ {f | TrialCollision r ω f.1}+ρ {f | TrialCollision r ω' f.2.2} := measure_union_le _ _
    _ ≤ G*p+H*q := by
      apply add_le_add
      · have hm := hP {f | TrialCollision r ω f}
        rw [Measure.fst,Measure.map_apply measurable_fst h₁,Measure.smul_apply,smul_eq_mul] at hm
        exact hm.trans (mul_le_mul' le_rfl hp)
      · have hm := hQ {f | TrialCollision r ω' f}
        rw [Measure.map_apply (by fun_prop) h₂,Measure.smul_apply,smul_eq_mul] at hm
        exact hm.trans (mul_le_mul' le_rfl hq)

end HardSphere.Bridge

end
end

end

end OAI
