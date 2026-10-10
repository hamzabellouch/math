import OAI.Probability.SpanningForest.ContinuousPathSampler
import OAI.Probability.SpanningForest.InnovationMartingale

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem336.RawInnovationSampler

variable {I Ω : Type*}

def observation (X : Ω → I → Bool) (B : I → ℝ≥0 → Ω → ℝ)
    (ω : Ω) (i : I) (t : ℝ≥0) : ℝ :=
  (t : ℝ) * bitValue (X ω i) + B i t ω

def rawInnovation (X : Ω → I → Bool) (B : I → ℝ≥0 → Ω → ℝ)
    (b : ℝ → (I → ℝ) → I → ℝ) (ω : Ω) (i : I) (t : ℝ≥0) : ℝ :=
  Innovation.nnInnovation (fun ω => bitValue (X ω i)) (B i)
    (fun s ω => b s (fun j => observation X B ω j s.toNNReal) i) t ω

@[simp]
lemma rawInnovation_apply (X : Ω → I → Bool) (B : I → ℝ≥0 → Ω → ℝ)
    (b : ℝ → (I → ℝ) → I → ℝ) (ω : Ω) (i : I) (t : ℝ≥0) :
    rawInnovation X B b ω i t = observation X B ω i t -
      ∫ s in (0 : ℝ)..t, b s (fun j => observation X B ω j s.toNNReal) i := by
  simp only [rawInnovation, Innovation.nnInnovation_apply, observation]

theorem hasLaw_of_raw_innovation [Countable I]
    [MeasurableSpace Ω] {Ω' : Type*} [MeasurableSpace Ω']
    [MeasurableSpace C(ℝ≥0, ℝ)] [BorelSpace C(ℝ≥0, ℝ)]
    {P : Measure Ω} {P' : Measure Ω'}
    {ρ : Measure (I → C(ℝ≥0, ℝ))} {ν : Measure (I → Bool)}
    {X : Ω → I → Bool} (hX : HasLaw X ν P)
    {B : I → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsBrownianReal (B i) P)
    (b : ℝ → (I → ℝ) → I → ℝ)
    (hb : ∀ i, Measurable (fun p : ℝ × (I → ℝ) => b p.1 p.2 i))
    (hbound : ∀ t y i, |b t y i| ≤ 1)
    {L : ℝ} (hL : 0 ≤ L)
    (hresponse : ∀ t y z D, 0 ≤ D → (∀ j, |y j - z j| ≤ D) →
      ∀ i, |b t y i - b t z i| ≤ L * D)
    (hinnovation : HasLaw (rawInnovation X B b) (ρ.map ContinuousPathLaw.raw) P)
    {fresh : Ω' → I → C(ℝ≥0, ℝ)} (hfresh : HasLaw fresh ρ P') :
    HasLaw (fun ω => PicardSampler.NonnegativeTime.sample
      ContinuousPathLaw.raw b (fresh ω)) ν P' := by
  have hBc : ∀ᵐ ω ∂P, ∀ i, Continuous (fun t => B i t ω) :=
    ae_all_iff.mpr (fun i => (hB i).cont)
  have hYc : ∀ᵐ ω ∂P, ∀ i, Continuous (observation X B ω i) := by
    filter_upwards [hBc] with ω hω
    intro i
    exact (continuous_subtype_val.mul continuous_const).add (hω i)
  have hIc : ∀ᵐ ω ∂P, ∀ i, Continuous (rawInnovation X B b ω i) := by
    filter_upwards [hYc] with ω hω
    intro i
    have hm : Measurable (fun s : ℝ =>
        b s (fun j => observation X B ω j s.toNNReal) i) :=
      (hb i).comp (measurable_id.prodMk (Measurable.of_eval (fun j => ((hω j).comp continuous_real_toNNReal).measurable)))
    have hi : Continuous (fun t : ℝ => ∫ s in (0 : ℝ)..t,
        b s (fun j => observation X B ω j s.toNNReal) i) :=
      intervalIntegral.continuous_primitive
        (Picard.intervalIntegrable_of_measurable_bounded hm
          (fun s => hbound s _ i)) 0
    change Continuous (fun t => rawInnovation X B b ω i t)
    simp_rw [rawInnovation_apply]
    exact (hω i).sub (hi.comp continuous_subtype_val)
  apply ContinuousPathSampler.hasLaw_of_raw_integral_coupling hX
    (fun i => (hB i).toIsPreBrownianReal) (rawInnovation X B b)
    (fun i t => (measurable_pi_apply t).comp_aemeasurable
      ((measurable_pi_apply i).comp_aemeasurable hinnovation.aemeasurable)) hIc hinnovation.map_eq hfresh
    b hb hbound hL hresponse (observation X B)
  · filter_upwards [hYc] with ω hω
    exact fun i => (hω i).measurable
  · exact Eventually.of_forall (fun ω t i => by rw [rawInnovation_apply]; ring)
  · exact Eventually.of_forall (fun _ _ _ => rfl)

end Problem336.RawInnovationSampler

end

end OAI
