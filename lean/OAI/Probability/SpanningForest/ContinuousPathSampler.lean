import OAI.Probability.SpanningForest.ContinuousPathLaw
import OAI.Probability.SpanningForest.PicardNonnegativeSampler

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem336.ContinuousPathSampler

variable {I : Type*}
  [MeasurableSpace C(ℝ≥0, ℝ)] [BorelSpace C(ℝ≥0, ℝ)]

lemma measurable_raw_eval (i : I) :
    Measurable (fun p : (I → C(ℝ≥0, ℝ)) × ℝ≥0 =>
      ContinuousPathLaw.raw p.1 i p.2) := by
  have hm : Measurable (fun p : (I → C(ℝ≥0, ℝ)) × ℝ≥0 => (p.1 i, p.2)) :=
    ((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd
  exact (show Continuous (fun p : C(ℝ≥0, ℝ) × ℝ≥0 => p.1 p.2) by
    fun_prop).measurable.comp hm

theorem hasLaw_of_raw_integral_coupling [Countable I]
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'}
    {ρ : Measure (I → C(ℝ≥0, ℝ))} {ν : Measure (I → Bool)}
    {X : Ω → I → Bool} (hX : HasLaw X ν P)
    {B : I → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) P)
    (U : Ω → I → ℝ≥0 → ℝ)
    (hU : ∀ i t, AEMeasurable (fun ω => U ω i t) P)
    (hUc : ∀ᵐ ω ∂P, ∀ i, Continuous (U ω i))
    (hUlaw : P.map U = ρ.map ContinuousPathLaw.raw)
    {fresh : Ω' → I → C(ℝ≥0, ℝ)} (hfresh : HasLaw fresh ρ P')
    (b : ℝ → (I → ℝ) → I → ℝ)
    (hb : ∀ i, Measurable (fun p : ℝ × (I → ℝ) => b p.1 p.2 i))
    (hbound : ∀ t y i, |b t y i| ≤ 1)
    {L : ℝ} (hL : 0 ≤ L)
    (hresponse : ∀ t y z D, 0 ≤ D → (∀ j, |y j - z j| ≤ D) →
      ∀ i, |b t y i - b t z i| ≤ L * D)
    (Y : Ω → I → ℝ≥0 → ℝ)
    (hY : ∀ᵐ ω ∂P, ∀ i, Measurable (Y ω i))
    (heq : ∀ᵐ ω ∂P, ∀ (t : ℝ≥0) i,
      Y ω i t = U ω i t +
        ∫ s in (0 : ℝ)..(t : ℝ), b s (fun j => Y ω j (Real.toNNReal s)) i)
    (hobs : ∀ᵐ ω ∂P, ∀ i (n : ℕ),
      Y ω i n = (n : ℝ) * bitValue (X ω i) + B i (n : ℝ≥0) ω) :
    HasLaw (fun ω => PicardSampler.NonnegativeTime.sample
      ContinuousPathLaw.raw b (fresh ω)) ν P' := by
  obtain ⟨V, hVm, hVeq, hVlaw⟩ :=
    ContinuousPathLaw.exists_measurable_lift_with_law U hU hUc hUlaw
  have hV : HasLaw V ρ P := ⟨hVm.aemeasurable, hVlaw⟩
  apply PicardSampler.NonnegativeTime.hasLaw_of_integral_coupling hX hB hV hfresh
    ContinuousPathLaw.raw b measurable_raw_eval hb hbound hL hresponse Y
  · filter_upwards [hY] with ω hω
    exact ⟨fun i => (V ω i).continuous, hω⟩
  · filter_upwards [heq, hVeq] with ω hω hvω
    intro t i
    rw [show ContinuousPathLaw.raw (V ω) i t = U ω i t from
      congrFun (congrFun hvω i) t]
    exact hω t i
  · exact hobs

end Problem336.ContinuousPathSampler

end

end OAI
