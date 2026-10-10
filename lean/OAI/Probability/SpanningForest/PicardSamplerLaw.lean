import OAI.Probability.SpanningForest.PicardUniqueness
import OAI.Probability.SpanningForest.BitRecovery

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace Problem336.PicardSampler

def decodedIntegers {I W : Type*} (w : W → I → ℝ → ℝ)
    (b : ℝ → (I → ℝ) → I → ℝ) (q : W) : I → ℕ → ℝ :=
  fun i n => Picard.decode (w q) b i n

def sample {I W : Type*} (w : W → I → ℝ → ℝ)
    (b : ℝ → (I → ℝ) → I → ℝ) (q : W) : I → Bool :=
  configurationReadout (decodedIntegers w b q)

lemma sample_apply_unshifted {I W : Type*}
    (w : W → I → ℝ → ℝ) (b : ℝ → (I → ℝ) → I → ℝ) (q : W) (i : I) :
    sample w b q i =
      if (1 / 2 : ℝ) < limsup
        (fun n : ℕ => Picard.decode (w q) b i n / (n : ℝ)) atTop
      then true else false := by
  have hshift := Filter.limsup_nat_add
    (fun n : ℕ => Picard.decode (w q) b i n / (n : ℝ)) 1
  simpa only [sample, configurationReadout, decodedIntegers, slopeReadout,
    Nat.cast_add, Nat.cast_one] using
    congrArg (fun r : ℝ => if (1 / 2 : ℝ) < r then true else false) hshift

lemma measurable_decodedIntegers {I W : Type*} [MeasurableSpace W]
    (w : W → I → ℝ → ℝ) (b : ℝ → (I → ℝ) → I → ℝ)
    (hw : ∀ i, Measurable (fun p : W × ℝ => w p.1 i p.2))
    (hb : ∀ i, Measurable (fun p : ℝ × (I → ℝ) => b p.1 p.2 i)) :
    Measurable (decodedIntegers w b) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro n
  have hd := Picard.measurable_decode w (fun _ => b) hw
    (fun i => (hb i).comp measurable_snd) i
  exact hd.comp (measurable_id.prodMk measurable_const)

lemma measurable_sample {I W : Type*} [MeasurableSpace W]
    (w : W → I → ℝ → ℝ) (b : ℝ → (I → ℝ) → I → ℝ)
    (hw : ∀ i, Measurable (fun p : W × ℝ => w p.1 i p.2))
    (hb : ∀ i, Measurable (fun p : ℝ × (I → ℝ) => b p.1 p.2 i)) :
    Measurable (sample w b) :=
  measurable_configurationReadout.comp (measurable_decodedIntegers w b hw hb)

theorem hasLaw_of_slope_coupling
    {I Ω W Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace W] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {ρ : Measure W} {ν : Measure (I → Bool)}
    {X : Ω → I → Bool} (hX : HasLaw X ν P)
    {innovation : Ω → W} (hinnovation : HasLaw innovation ρ P)
    {fresh : Ω' → W} (hfresh : HasLaw fresh ρ P')
    (w : W → I → ℝ → ℝ) (b : ℝ → (I → ℝ) → I → ℝ)
    (hw : ∀ i, Measurable (fun p : W × ℝ => w p.1 i p.2))
    (hb : ∀ i, Measurable (fun p : ℝ × (I → ℝ) => b p.1 p.2 i))
    (hbound : ∀ t y i, |b t y i| ≤ 1)
    {L : ℝ} (hL : 0 ≤ L)
    (hresponse : ∀ t y y' D, 0 ≤ D → (∀ j, |y j - y' j| ≤ D) →
      ∀ i, |b t y i - b t y' i| ≤ L * D)
    (Y : Ω → I → ℝ → ℝ)
    (hpaths : ∀ᵐ ω ∂P, (∀ i, Continuous (w (innovation ω) i)) ∧
      (∀ i, Measurable (Y ω i)))
    (heq : ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → ∀ i,
      Y ω i t = w (innovation ω) i t +
        ∫ s in (0 : ℝ)..t, b s (fun j => Y ω j s) i)
    (hslopes : ∀ᵐ ω ∂P, ∀ i,
      Tendsto (fun n : ℕ => Y ω i (n + 1 : ℕ) / (n + 1 : ℝ)) atTop
        (𝓝 (bitValue (X ω i)))) :
    HasLaw (fun ω => sample w b (fresh ω)) ν P' := by
  have href : HasLaw (fun ω => sample w b (innovation ω)) ν P := by
    apply hX.congr
    filter_upwards [hpaths, heq, hslopes] with ω hp he hs
    funext i
    have hinv := Picard.decode_eq_solution (w (innovation ω)) (Y ω) b hp.1 hp.2
      hb hbound hL hresponse he
    change slopeReadout (fun n : ℕ => Picard.decode (w (innovation ω)) b i n) = X ω i
    have hseq : (fun n : ℕ => Picard.decode (w (innovation ω)) b i n) =
        (fun n : ℕ => Y ω i n) := by
      funext n
      exact hinv i n (Nat.cast_nonneg n)
    rw [hseq]
    exact slopeReadout_of_tendsto (hs i)
  exact HasLaw.comp_of_hasLaw_comp (f := sample w b)
    (measurable_sample w b hw hb).aemeasurable hinnovation hfresh href

theorem hasLaw_of_integral_coupling
    {I Ω W Ω' : Type*} [Countable I]
    [MeasurableSpace Ω] [MeasurableSpace W] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {ρ : Measure W} {ν : Measure (I → Bool)}
    {X : Ω → I → Bool} (hX : HasLaw X ν P)
    {B : I → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) P)
    {innovation : Ω → W} (hinnovation : HasLaw innovation ρ P)
    {fresh : Ω' → W} (hfresh : HasLaw fresh ρ P')
    (w : W → I → ℝ → ℝ) (b : ℝ → (I → ℝ) → I → ℝ)
    (hw : ∀ i, Measurable (fun p : W × ℝ => w p.1 i p.2))
    (hb : ∀ i, Measurable (fun p : ℝ × (I → ℝ) => b p.1 p.2 i))
    (hbound : ∀ t y i, |b t y i| ≤ 1)
    {L : ℝ} (hL : 0 ≤ L)
    (hresponse : ∀ t y y' D, 0 ≤ D → (∀ j, |y j - y' j| ≤ D) →
      ∀ i, |b t y i - b t y' i| ≤ L * D)
    (Y : Ω → I → ℝ → ℝ)
    (hpaths : ∀ᵐ ω ∂P, (∀ i, Continuous (w (innovation ω) i)) ∧
      (∀ i, Measurable (Y ω i)))
    (heq : ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → ∀ i,
      Y ω i t = w (innovation ω) i t +
        ∫ s in (0 : ℝ)..t, b s (fun j => Y ω j s) i)
    (hobs : ∀ᵐ ω ∂P, ∀ i (n : ℕ),
      Y ω i n = (n : ℝ) * bitValue (X ω i) + B i (n : ℝ≥0) ω) :
    HasLaw (fun ω => sample w b (fresh ω)) ν P' := by
  apply sampler_hasLaw_of_brownian_inversion hX hB hinnovation hfresh
    (measurable_decodedIntegers w b hw hb)
  filter_upwards [hpaths, heq, hobs] with ω hp he ho
  funext i n
  exact (Picard.decode_eq_solution (w (innovation ω)) (Y ω) b hp.1 hp.2
    hb hbound hL hresponse he i n (Nat.cast_nonneg n)).trans (ho i n)

def observation {I Ω : Type*} (X : Ω → I → Bool)
    (B : I → ℝ≥0 → Ω → ℝ) (ω : Ω) (i : I) (t : ℝ) : ℝ :=
  t * bitValue (X ω i) + B i (Real.toNNReal t) ω

theorem hasLaw_of_brownian_innovation
    {I Ω W Ω' : Type*} [Countable I]
    [MeasurableSpace Ω] [MeasurableSpace W] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {ρ : Measure W} {ν : Measure (I → Bool)}
    {X : Ω → I → Bool} (hX : HasLaw X ν P)
    {B : I → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsBrownianReal (B i) P)
    {innovation : Ω → W} (hinnovation : HasLaw innovation ρ P)
    {fresh : Ω' → W} (hfresh : HasLaw fresh ρ P')
    (w : W → I → ℝ → ℝ) (b : ℝ → (I → ℝ) → I → ℝ)
    (hw : ∀ i, Measurable (fun p : W × ℝ => w p.1 i p.2))
    (hwcont : ∀ᵐ ω ∂P, ∀ i, Continuous (w (innovation ω) i))
    (hb : ∀ i, Measurable (fun p : ℝ × (I → ℝ) => b p.1 p.2 i))
    (hbound : ∀ t y i, |b t y i| ≤ 1)
    {L : ℝ} (hL : 0 ≤ L)
    (hresponse : ∀ t y y' D, 0 ≤ D → (∀ j, |y j - y' j| ≤ D) →
      ∀ i, |b t y i - b t y' i| ≤ L * D)
    (hinnovation_eq : ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → ∀ i,
      w (innovation ω) i t = observation X B ω i t -
        ∫ s in (0 : ℝ)..t, b s (fun j => observation X B ω j s) i) :
    HasLaw (fun ω => sample w b (fresh ω)) ν P' := by
  apply hasLaw_of_integral_coupling hX (fun i => (hB i).toIsPreBrownianReal)
    hinnovation hfresh w b hw hb hbound hL hresponse (observation X B)
  · have hcont : ∀ᵐ ω ∂P, ∀ i, Continuous (fun t => B i t ω) :=
      ae_all_iff.mpr (fun i => (hB i).cont)
    filter_upwards [hwcont, hcont] with ω hwω hBω
    refine ⟨hwω, fun i => ?_⟩
    exact ((continuous_id.mul continuous_const).add
      ((hBω i).comp continuous_real_toNNReal)).measurable
  · filter_upwards [hinnovation_eq] with ω hω
    intro t ht i
    have h := hω t ht i
    linarith
  · apply Eventually.of_forall
    intro ω i n
    simp only [observation, Real.toNNReal_natCast]

end Problem336.PicardSampler

end

end OAI
