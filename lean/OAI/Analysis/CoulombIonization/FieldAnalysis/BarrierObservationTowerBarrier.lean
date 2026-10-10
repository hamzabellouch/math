import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.Conditional
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierMasterRegularityBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric ProbabilityTheory
open scoped BigOperators Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis CoulombObservation
attribute [local instance] physicalObservationLaw_probability
attribute [local irreducible] masterKernel masterWidth scaledRealPacket

lemma ae_forall_eq_of_continuous {D : Type*} [MeasurableSpace D] {P : Measure D}
    {u v : D → TFSpace → ℝ} (hu : ∀ᵐ d ∂P, Continuous (u d))
    (hv : ∀ᵐ d ∂P, Continuous (v d))
    (he : ∀ x, ∀ᵐ d ∂P, u d x = v d x) :
    ∀ᵐ d ∂P, ∀ x, u d x = v d x := by
  obtain ⟨S,hSc,hSd⟩ := TopologicalSpace.exists_countable_dense TFSpace
  let : Countable S := hSc.to_subtype
  have hS : ∀ᵐ d ∂P, ∀ x : S, u d x = v d x := ae_all_iff.mpr (fun x => he x)
  filter_upwards [hu,hv,hS] with d hud hvd hSd'
  have hfun : u d = v d := Continuous.ext_on hSd hud hvd (fun x hx => hSd' ⟨x,hx⟩)
  exact congrFun hfun

lemma conditionalField_eq_condExp {Ω D : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] [Nonempty Ω] [MeasurableSpace D]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → D} (hX : Measurable X)
    {u : Ω → TFSpace → ℝ} (hu : Measurable (Function.uncurry u))
    (hub : DeterministicLocalBound u) (x : TFSpace) :
    P[(fun sample => u sample x) | MeasurableSpace.comap X inferInstance] =ᵐ[P]
      fun sample => conditionalField P X u (X sample) x := by
  have hm : StronglyMeasurable (fun sample => u sample x) :=
    (hu.comp (measurable_id.prodMk measurable_const)).stronglyMeasurable
  have hi := deterministicBound_integrable_section (P := P) hu hub x
  simpa only [conditionalField,Function.comp_def,id_eq] using
    (condExp_ae_eq_integral_condDistrib hX measurable_id.aemeasurable hm hi)

def originalMasterField {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) (c₁ r₀ s : ℝ) (g : Space → ℝ)
    (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) (y : Space) : ℝ :=
  jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j z) y

lemma originalMasterField_measurable {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) {g : Space → ℝ} (hg : Continuous g) :
    Measurable (Function.uncurry (originalMasterField μ ell j c₁ r₀ s g)) :=
  (jointMasterPosterior_measurable μ ell j hc hr hs hg).comp
    (((originalDatum_measurable ell j).comp measurable_fst).prodMk measurable_snd)

lemma originalMasterField_deterministicBound {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (hrs : r₀ ≤ s)
    {g : Space → ℝ} (hg : Continuous g) (hcg : HasCompactSupport g) :
    DeterministicLocalBound (originalMasterField μ ell j c₁ r₀ s g) := by
  obtain ⟨C,_,hC⟩ := jointMasterPosterior_global_bound μ ell j hc hr hs hrs hg hcg
  exact fun _ _ => ⟨C,fun z y _ => hC (originalDatum ell j z) y⟩

lemma originalMasterField_continuous {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (hrs : r₀ ≤ s)
    {g : Space → ℝ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) :
    Continuous (originalMasterField μ ell j c₁ r₀ s g z) :=
  jointMasterPosterior_continuous μ ell j hc hr hs hrs hg hcg (originalDatum ell j z)

theorem originalMasterField_tower {N K : ℕ} (μ : Measure (Configuration N))
    [IsProbabilityMeasure μ] (ell : Fin K → ℝ) {j k : ℕ} (hjk : j ≤ k) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (hrs : r₀ ≤ s)
    {g : Space → ℝ} (hg : Continuous g) (hcg : HasCompactSupport g) :
    ∀ᵐ z ∂physicalObservationLaw μ K, ∀ y,
      conditionalField (physicalObservationLaw μ K) (originalDatum ell k)
        (originalMasterField μ ell j c₁ r₀ s g) (originalDatum ell k z) y =
      originalMasterField μ ell k c₁ r₀ s g z y := by
  let P := physicalObservationLaw μ K
  have hPm := originalMasterField_measurable μ ell j hc hr hs hg
  have hPb := originalMasterField_deterministicBound μ ell j hc hr hs hrs hg hcg
  have hPc := originalMasterField_continuous μ ell j hc hr hs hrs hg hcg
  apply ae_forall_eq_of_continuous
  · have hh := conditionalField_continuous P (originalDatum ell k)
      (originalDatum_measurable ell k) hPm hPb (Eventually.of_forall hPc)
    exact ae_of_ae_map (originalDatum_measurable ell k).aemeasurable hh
  · exact Eventually.of_forall (originalMasterField_continuous μ ell k hc hr hs hrs hg hcg)
  intro y
  have hce := conditionalField_eq_condExp P (originalDatum_measurable ell k) hPm hPb y
  rw [originalDatum_comap] at hce
  have hquery : Measurable (fun x => masterKernel c₁ r₀ s g x y) :=
    (masterKernel_joint_continuous hc hr hs hg).measurable.comp (measurable_id.prodMk measurable_const)
  have hrawm : Measurable (fun z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) =>
      ∑ i, masterKernel c₁ r₀ s g (z.1 i) y) :=
    Finset.measurable_sum _ (fun i _ => hquery.comp ((measurable_pi_apply i).comp measurable_fst))
  obtain ⟨C,_,hC⟩ := masterConfigurationDensity_bound (N := N) hc hr hs hrs hg hcg
  have hrawi : Integrable (fun z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) =>
      ∑ i, masterKernel c₁ r₀ s g (z.1 i) y) P :=
    Integrable.of_bound hrawm.aestronglyMeasurable C (Eventually.of_forall fun z => hC z.1 y)
  exact hce.symm.trans (kernelPosteriorTest_tower μ ell hjk hquery hrawi)

end CoulombBarrier

end

end OAI
