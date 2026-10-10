import OAI.NumberTheory.DukePrimeDegree.Entropy.ObservationInformation
import OAI.NumberTheory.DukePrimeDegree.Entropy.FiniteLabelEntropy
import OAI.NumberTheory.DukePrimeDegree.Entropy.InfiniteLabelEntropy

namespace OAI

/-! # Pointwise information after finite transverse conditioning -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

theorem conditionalEntropy_transverse_label_information
    {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    [StandardBorelSpace T] [Nonempty T]
    (ρ : Measure (S × T)) [IsFiniteMeasure ρ]
    {M N : ℕ} {P : S × T → Fin M} (hP : Measurable P)
    {Q : S × T → Fin N} (hQ : Measurable Q) :
    conditionalSigmaEntropy ρ P (transverseLabelSigma Q) =
      ∫ z, observationInformation ((ρ.map (finiteLabelLift Q)).condKernel (z.1,Q z))
        (fun t => P (z.1,t)) z.2 ∂ρ := by
  let σ := ρ.map (finiteLabelLift Q)
  let κ := σ.condKernel
  let R : (S × Fin N) × T → Fin M := fun z => P (z.1.1,z.2)
  have hR : ∀ a, MeasurableSet {z | R z=a} := fun a =>
    (hP.comp (measurable_fst.fst.prodMk measurable_snd)) (measurableSet_singleton a)
  let E : S × Fin N → ℝ := fun s => observationEntropy (κ s) (fun t => R (s,t))
  let I : (S × Fin N) × T → ℝ :=
    fun z => observationInformation (κ z.1) (fun t => R (z.1,t)) z.2
  have hE : Measurable E := measurable_fiber_observationEntropy κ R hR
  have hI : Measurable I := measurable_kernel_observationInformation κ R hR
  have H := Measure.integral_compProd (integrable_kernel_observationInformation σ.fst κ R hR)
  change (∫ z, I z ∂(σ.fst ⊗ₘ σ.condKernel)) = _ at H
  rw [Measure.disintegrate] at H
  have HI : (∫ z, I z ∂σ) = ∫ s, E s ∂σ.fst := by
    refine H.trans (integral_congr_ae (ae_of_all _ fun s => ?_))
    exact integral_observationInformation (κ s) _
      (fun a => (hR a).preimage measurable_prodMk_left)
  calc
    _ = ∫ z, E (z.1,Q z) ∂ρ := conditionalEntropy_transverse_label ρ hP hQ
    _ = ∫ z, E z.1 ∂σ :=
      (integral_map (finiteLabelLift_measurable hQ).aemeasurable
        (hE.comp measurable_fst).aestronglyMeasurable).symm
    _ = ∫ s, E s ∂σ.fst :=
      (integral_map measurable_fst.aemeasurable hE.aestronglyMeasurable).symm
    _ = ∫ z, I z ∂σ := HI.symm
    _ = _ := integral_map (finiteLabelLift_measurable hQ).aemeasurable hI.aestronglyMeasurable

theorem conditionalEntropy_transverse_label_information_restriction
    {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    [StandardBorelSpace T] [Nonempty T]
    (ρ : Measure (S × T)) [IsFiniteMeasure ρ]
    {M N : ℕ} {P : S × T → Fin M} (hP : Measurable P)
    {Q : S × T → Fin N} (hQ : Measurable Q) :
    conditionalSigmaEntropy ρ P (transverseLabelSigma Q) =
      ∫ z, observationInformation
        ((anchorNormalize (ρ.condKernel z.1) {t | Q (z.1,t)=Q z}).restrict
          {t | Q (z.1,t)=Q z}) (fun t => P (z.1,t)) z.2 ∂ρ := by
  rw [conditionalEntropy_transverse_label_information ρ hP hQ]
  apply integral_congr_ae
  filter_upwards [finiteLabelLift_condKernel ρ hQ] with z hz
  rw [hz.2]

end DukePrimeDegree

end

end OAI
