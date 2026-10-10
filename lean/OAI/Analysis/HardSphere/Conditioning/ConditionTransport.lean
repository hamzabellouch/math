import Mathlib
import OAI.Analysis.HardSphere.Bridges.LocalReference
import OAI.Analysis.HardSphere.Conditioning.ProductNormalize

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Comparison
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
lemma conditioned_map_preimage (μ : Measure X) (f : X→Y) (hf : Measurable f)
    {S : Set Y} (hS : MeasurableSet S) :
    (conditionedMeasure μ (f⁻¹' S)).map f=conditionedMeasure (μ.map f) S := by
  unfold conditionedMeasure
  rw [Measure.map_smul _ hf.aemeasurable,Measure.map_apply hf hS]
  congr 1
  ext B hB
  rw [Measure.map_apply hf hB,Measure.restrict_apply (hB.preimage hf),
    Measure.restrict_apply hB,Measure.map_apply hf (hB.inter hS)]
  rfl

lemma conditioned_map_ae (μ : Measure X) (f : X→Y) (hf : Measurable f)
    (E : Set X) {S : Set Y} (hS : MeasurableSet S) (hE : E=ᵐ[μ] f⁻¹' S) :
    (conditionedMeasure μ E).map f=conditionedMeasure (μ.map f) S := by
  have he : conditionedMeasure μ E=conditionedMeasure μ (f⁻¹' S) := by
    unfold conditionedMeasure
    rw [measure_congr hE,Measure.restrict_congr_set hE]
  rw [he]
  exact conditioned_map_preimage μ f hf hS

lemma conditioned_pi_map {I : Type*} [Fintype I] {X Y : I→Type*}
    [∀i,MeasurableSpace (X i)] [∀i,MeasurableSpace (Y i)]
    (μ : ∀i,Measure (X i)) [∀i,IsFiniteMeasure (μ i)]
    (f : ∀i,X i→Y i) (hf : ∀i,Measurable (f i))
    {S : Set (∀i,Y i)} (hS : MeasurableSet S) :
    (conditionedMeasure (Measure.pi μ) ((fun x i ↦ f i (x i))⁻¹' S)).map
      (fun x i ↦ f i (x i))=
      conditionedMeasure (Measure.pi fun i ↦ (μ i).map (f i)) S := by
  have hmf : Measurable (fun x : ∀i,X i ↦ fun i ↦ f i (x i)) := by
    exact Measurable.of_eval (fun i ↦ (hf i).comp (measurable_pi_apply i))
  rw [conditioned_map_preimage _ _ hmf hS,Measure.pi_map_pi (fun i ↦ (hf i).aemeasurable)]
end HardSphere.Comparison
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison

lemma noise_reference_identification (t : ℝ) (y z : Point) (E : Set Noise)
    {S : Set C(Time,Point)} (hS : MeasurableSet S)
    (hE : E=ᵐ[law] (leg (2*t) y z)⁻¹' S) :
    (conditionedMeasure law E).map (leg (2*t) y z)=individualReference t y z S :=
  conditioned_map_ae law _ (leg_continuous _ _ _).measurable E hS hE

end HardSphere.Bridge

end
end

end

end OAI
