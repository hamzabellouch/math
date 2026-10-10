import OAI.Probability.SpanningForest.PicardNonnegativeTime
import OAI.Probability.SpanningForest.PicardSamplerLaw

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace Problem336.PicardSampler.NonnegativeTime

open Picard.NonnegativeTime

def sample {I W : Type*} (w : W → I → ℝ≥0 → ℝ)
    (b : ℝ → (I → ℝ) → I → ℝ) (q : W) : I → Bool :=
  PicardSampler.sample (fun q => extendInput (w q)) b q

theorem measurable_sample {I W : Type*} [MeasurableSpace W]
    (w : W → I → ℝ≥0 → ℝ) (b : ℝ → (I → ℝ) → I → ℝ)
    (hw : ∀ i, Measurable (fun p : W × ℝ≥0 => w p.1 i p.2))
    (hb : ∀ i, Measurable (fun p : ℝ × (I → ℝ) => b p.1 p.2 i)) :
    Measurable (sample w b) :=
  PicardSampler.measurable_sample _ b (measurable_extendInput w hw) hb

theorem measurable_sample_parameterized {I W : Type*} [MeasurableSpace W]
    (w : W → I → ℝ≥0 → ℝ) (b : W → ℝ → (I → ℝ) → I → ℝ)
    (hw : ∀ i, Measurable (fun p : W × ℝ≥0 => w p.1 i p.2))
    (hb : ∀ i, Measurable
      (fun p : W × (ℝ × (I → ℝ)) => b p.1 p.2.1 p.2.2 i)) :
    Measurable (fun q => sample w (b q) q) := by
  have hz : Measurable (fun q i (n : ℕ) =>
      Picard.decode (extendInput (w q)) (b q) i (n : ℝ)) := by
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro n
    have hm : Measurable (fun p : W × ℝ =>
        Picard.decode (extendInput (w p.1)) (b p.1) i p.2) :=
      @Picard.measurable_decode I W _ (fun q => extendInput (w q)) b
        (measurable_extendInput w hw) hb i
    have hc : Measurable (fun q : W => (q, (n : ℝ))) :=
      measurable_id.prodMk measurable_const
    convert hm.comp hc using 1
    rfl
  exact measurable_configurationReadout.comp hz

theorem sample_relabel {I J W W' : Type*} (e : I ≃ J)
    (w : W → I → ℝ≥0 → ℝ) (w' : W' → J → ℝ≥0 → ℝ)
    (b : ℝ → (I → ℝ) → I → ℝ) (b' : ℝ → (J → ℝ) → J → ℝ)
    (q : W) (q' : W')
    (hw : ∀ i t, w' q' (e i) t = w q i t)
    (hb : ∀ t (y : I → ℝ) i,
      b' t (fun j => y (e.symm j)) (e i) = b t y i)
    (i : I) : sample w' b' q' (e i) = sample w b q i := by
  change slopeReadout (fun n : ℕ =>
    Picard.decode (extendInput (w' q')) b' (e i) n) =
      slopeReadout (fun n : ℕ => Picard.decode (extendInput (w q)) b i n)
  congr 1
  funext n
  exact Picard.decode_relabel e (extendInput (w q)) (extendInput (w' q')) b b'
    (fun j t => hw j (Real.toNNReal t)) hb i n

theorem hasLaw_of_integral_coupling
    {I Ω W Ω' : Type*} [Countable I]
    [MeasurableSpace Ω] [MeasurableSpace W] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {ρ : Measure W} {ν : Measure (I → Bool)}
    {X : Ω → I → Bool} (hX : HasLaw X ν P)
    {B : I → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) P)
    {innovation : Ω → W} (hinnovation : HasLaw innovation ρ P)
    {fresh : Ω' → W} (hfresh : HasLaw fresh ρ P')
    (w : W → I → ℝ≥0 → ℝ) (b : ℝ → (I → ℝ) → I → ℝ)
    (hw : ∀ i, Measurable (fun p : W × ℝ≥0 => w p.1 i p.2))
    (hb : ∀ i, Measurable (fun p : ℝ × (I → ℝ) => b p.1 p.2 i))
    (hbound : ∀ t y i, |b t y i| ≤ 1)
    {L : ℝ} (hL : 0 ≤ L)
    (hresponse : ∀ t y z D, 0 ≤ D → (∀ j, |y j - z j| ≤ D) →
      ∀ i, |b t y i - b t z i| ≤ L * D)
    (Y : Ω → I → ℝ≥0 → ℝ)
    (hpaths : ∀ᵐ ω ∂P, (∀ i, Continuous (w (innovation ω) i)) ∧
      (∀ i, Measurable (Y ω i)))
    (heq : ∀ᵐ ω ∂P, ∀ (t : ℝ≥0) i,
      Y ω i t = w (innovation ω) i t +
        ∫ s in (0 : ℝ)..(t : ℝ), b s (fun j => Y ω j (Real.toNNReal s)) i)
    (hobs : ∀ᵐ ω ∂P, ∀ i (n : ℕ),
      Y ω i n = (n : ℝ) * bitValue (X ω i) + B i (n : ℝ≥0) ω) :
    HasLaw (fun ω => sample w b (fresh ω)) ν P' := by
  apply PicardSampler.hasLaw_of_integral_coupling hX hB hinnovation hfresh
    (fun q => extendInput (w q)) b (measurable_extendInput w hw)
    hb hbound hL hresponse (fun ω => extendInput (Y ω))
  · filter_upwards [hpaths] with ω hω
    exact ⟨continuous_extendInput hω.1,
      fun i => (hω.2 i).comp continuous_real_toNNReal.measurable⟩
  · filter_upwards [heq] with ω hω
    intro t ht i
    simpa only [extendInput, Real.coe_toNNReal t ht] using hω (Real.toNNReal t) i
  · filter_upwards [hobs] with ω hω
    intro i n
    simpa only [extendInput, Real.toNNReal_natCast] using hω i n

end Problem336.PicardSampler.NonnegativeTime

end

end OAI
