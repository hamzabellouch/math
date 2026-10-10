import Mathlib
import OAI.Probability.GaussianRegression.Main
import OAI.Probability.ProjectionMoments.BorelRules
import OAI.Probability.MemoryPrecision.AmbientGram
import OAI.Probability.MemoryPrecision.KernelModel

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression

lemma aemeasurable_countable_select {X J Y : Type*} [MeasurableSpace X]
    [MeasurableSpace J] [MeasurableSingletonClass J] [Countable J] [MeasurableSpace Y]
    {μ : Measure X} {h : J → X → Y} (hh : ∀ j, AEMeasurable (h j) μ)
    {φ : X → J} (hφ : AEMeasurable φ μ) : AEMeasurable (fun x => h (φ x) x) μ := by
  have hmk : Measurable (fun x => (hh (hφ.mk φ x)).mk (h (hφ.mk φ x)) x) :=
    (measurable_from_prod_countable_right
      (f := fun z : J × X => (hh z.1).mk (h z.1) z.2)
      (fun j => (hh j).measurable_mk)).comp (hφ.measurable_mk.prodMk measurable_id)
  apply hmk.aemeasurable.congr
  have hall : ∀ᵐ x ∂μ, ∀ j, h j x = (hh j).mk (h j) x :=
    ae_all_iff.mpr (fun j => (hh j).ae_eq_mk)
  filter_upwards [hφ.ae_eq_mk, hall] with x hx hx'
  rw [← hx, ← hx']

lemma prior_observation_with_seed {X : Type v} [MeasurableSpace X]
    {d T : ℕ} (ν : Measure X) [SFinite ν] {Ω : Type u} [MeasurableSpace Ω]
    (ρ : Measure Ω) [SFinite ρ] (ι : X → UnitSphere d) (i : Fin T)
    (ho : Measure.QuasiMeasurePreserving
      (fun z : X × Samples d T => (z.2 i,⟪(ι z.1).val,z.2 i⟫))
      (ν.prod (sampleLaw d T)) (observationReference d)) :
    Measure.QuasiMeasurePreserving
      (fun z : X × (Ω × Samples d T) => (z.2.1,(z.2.2 i,⟪(ι z.1).val,z.2.2 i⟫)))
      (ν.prod (ρ.prod (sampleLaw d T))) (ρ.prod (observationReference d)) := by
  let : IsProbabilityMeasure (sampleLaw d T) := by unfold sampleLaw; infer_instance
  let : SigmaFinite (observationReference d) := by unfold observationReference; infer_instance
  have h1 := (MeasurePreserving.id ν).prod
    (Measure.measurePreserving_swap (μ := ρ) (ν := sampleLaw d T))
  have h2 := (measurePreserving_prodAssoc ν (sampleLaw d T) ρ).symm
    (MeasurableEquiv.prodAssoc : (X × Samples d T) × Ω ≃ᵐ X × (Samples d T × Ω))
  have h3 := (Measure.measurePreserving_swap (μ := ν.prod (sampleLaw d T)) (ν := ρ)).comp (h2.comp h1)
  have h4 := MeasureTheory.QuasiMeasurePreserving.prodMap (MeasurePreserving.id ρ).quasiMeasurePreserving ho
  convert h4.comp h3.quasiMeasurePreserving using 1
  rfl

lemma prior_estimate_aemeasurable {X : Type v} [MeasurableSpace X]
    {d M T : ℕ} (ν : Measure X) [SFinite ν] {Ω : Type u} [MeasurableSpace Ω]
    (ρ : Measure Ω) [SFinite ρ] (ι : X → UnitSphere d)
    (L : Learner d M T Ω) (hL : L.Admissible ρ)
    (ho : ∀ i : Fin T, Measure.QuasiMeasurePreserving
      (fun z : X × Samples d T => (z.2 i,⟪(ι z.1).val,z.2 i⟫))
      (ν.prod (sampleLaw d T)) (observationReference d)) :
    AEMeasurable (fun z : X × (Ω × Samples d T) => L.estimate (ι z.1) z.2.1 z.2.2)
      (ν.prod (ρ.prod (sampleLaw d T))) := by
  let μ := ν.prod (ρ.prod (sampleLaw d T))
  let : IsProbabilityMeasure (sampleLaw d T) := by unfold sampleLaw; infer_instance
  have hω : Measure.QuasiMeasurePreserving (fun z : X × (Ω × Samples d T) => z.2.1) μ ρ :=
    Measure.quasiMeasurePreserving_fst.comp Measure.quasiMeasurePreserving_snd
  have ht (t : ℕ) (a : State M) (i : Fin T) :
      AEMeasurable (fun z : X × (Ω × Samples d T) =>
        L.transition t z.2.1 a (z.2.2 i,⟪z.2.2 i,(ι z.1).val⟫)) μ := by
    have h := (hL.transition t a).comp_quasiMeasurePreserving
      (prior_observation_with_seed ν ρ ι i (ho i))
    simpa only [Function.comp_def, μ, real_inner_comm] using h
  have hr (n : ℕ) : AEMeasurable
      (fun z : X × (Ω × Samples d T) => L.run (ι z.1) z.2.1 z.2.2 n) μ := by
    induction n with
    | zero =>
      exact (measurable_of_countable (fun a : Bool × State M =>
        if a.1 then Sum.inr (0,a.2) else Sum.inl a.2)).comp_aemeasurable
          (hL.initialChoice.comp_quasiMeasurePreserving hω)
    | succ n ih =>
      let g : Learner.RunStatus M → (X × (Ω × Samples d T)) → Learner.RunStatus M := fun j z =>
        match j with
        | .inr done => .inr done
        | .inl a => if hn : n < T then
            let b := L.transition (n+1) z.2.1 a (z.2.2 ⟨n,hn⟩,⟪z.2.2 ⟨n,hn⟩,(ι z.1).val⟫)
            if b.1 then .inr (n+1,b.2) else .inl b.2
          else .inl a
      apply aemeasurable_countable_select (h := g) ?_ ih
      intro j
      cases j with
      | inr done => exact aemeasurable_const
      | inl a =>
        by_cases hn : n < T
        · simpa only [g, dite_eq_left hn, Function.comp_def] using
            (measurable_of_countable (fun b : Bool × State M =>
            if b.1 then Sum.inr (n+1,b.2) else Sum.inl b.2)).comp_aemeasurable (ht (n+1) a ⟨n,hn⟩)
        · simpa only [g, dite_eq_right hn] using (aemeasurable_const (b := Sum.inl a))
  have hterm : AEMeasurable
      (fun z : X × (Ω × Samples d T) => L.terminal (ι z.1) z.2.1 z.2.2) μ := by
    convert
      (measurable_of_countable (fun j : Learner.RunStatus M =>
        (match j with | .inl a => (T,a) | .inr p => p : ℕ × State M))).comp_aemeasurable (hr T) using 1
    rfl
  exact aemeasurable_countable_select
    (fun j : ℕ × State M => (hL.output j.1 j.2).comp_quasiMeasurePreserving hω) hterm
end MemoryPrecision


end

end OAI
