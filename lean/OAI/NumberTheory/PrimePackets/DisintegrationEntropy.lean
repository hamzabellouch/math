import OAI.NumberTheory.PrimePackets.ConditionalSigmaEntropy

namespace OAI

/-! # Conditional information in disintegration coordinates -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace PrimeDegreePackets

variable {S T α : Type*} [MeasurableSpace S] [MeasurableSpace T]
  [StandardBorelSpace T] [Nonempty T] [Fintype α]

omit [StandardBorelSpace T] [Nonempty T] in
lemma measurable_fiber_observationEntropy (κ : Kernel S T) [IsMarkovKernel κ]
    (P : S × T → α) (hP : ∀ a, MeasurableSet {z | P z = a}) :
    Measurable (fun s => observationEntropy (κ s) (fun t => P (s,t))) := by
  apply continuous_finiteShannon.measurable.comp
  apply measurable_pi_iff.mpr
  intro a
  exact (Kernel.measurable_kernel_prodMk_left (κ := κ) (hP a)).ennreal_toReal

omit [Fintype α] in
lemma condExp_fst_observation_probability
    (μ : Measure (S × T)) [IsFiniteMeasure μ]
    (P : S × T → α) (hP : ∀ a, MeasurableSet {z | P z = a}) (a : α) :
    μ[({z | P z = a}.indicator (fun _ => (1 : ℝ))) |
        MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace S)] =ᵐ[μ]
      fun z => (μ.condKernel z.1).real {t | P (z.1,t) = a} := by
  let f : S × T → ℝ := {z | P z = a}.indicator (fun _ => 1)
  have hid : (fun z : S × T => (z.1,z.2)) = id := rfl
  have hf : Integrable f (μ.map (fun z : S × T => (z.1,z.2))) := by
    rw [hid, Measure.map_id]
    exact (integrable_const (1 : ℝ)).indicator (hP a)
  have H := condExp_prod_ae_eq_integral_condDistrib'
    (μ := μ) (X := (Prod.fst : S × T → S)) (Y := (Prod.snd : S × T → T))
    measurable_fst measurable_snd.aemeasurable hf
  have hκ : condDistrib (Prod.snd : S × T → T) Prod.fst μ = μ.condKernel := by
    simp only [condDistrib, hid, Measure.map_id]
  rw [hκ] at H
  have hI (s : S) : (∫ t, f (s,t) ∂μ.condKernel s) =
      (μ.condKernel s).real {t | P (s,t) = a} := by
    change (∫ t, {t | P (s,t) = a}.indicator (fun _ => (1 : ℝ)) t ∂μ.condKernel s) = _
    have hs : MeasurableSet {t | P (s,t) = a} := (hP a).preimage measurable_prodMk_left
    rw [integral_indicator_const _ hs]
    simp only [smul_eq_mul, mul_one]
  simpa only [Prod.eta, hI] using H

theorem conditionalSigmaEntropy_fst
    (μ : Measure (S × T)) [IsFiniteMeasure μ]
    (P : S × T → α) (hP : ∀ a, MeasurableSet {z | P z = a}) :
    conditionalSigmaEntropy μ P
        (MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace S)) =
      ∫ s, observationEntropy (μ.condKernel s) (fun t => P (s,t)) ∂μ.fst := by
  have H := ae_all_iff.mpr (fun a => condExp_fst_observation_probability μ P hP a)
  unfold conditionalSigmaEntropy
  calc
    _ = ∫ z, observationEntropy (μ.condKernel z.1) (fun t => P (z.1,t)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [H] with z hz
      unfold observationEntropy
      congr 1
      exact funext hz
    _ = _ := by
      exact (integral_map measurable_fst.aemeasurable
        (measurable_fiber_observationEntropy μ.condKernel P hP).aestronglyMeasurable).symm

end PrimeDegreePackets

end

end OAI
