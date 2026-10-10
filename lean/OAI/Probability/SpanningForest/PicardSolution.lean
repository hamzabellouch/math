import OAI.Probability.SpanningForest.Picard
import OAI.Probability.SpanningForest.PicardBounds

namespace OAI

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace Problem336.Picard

variable {ι : Type*}

lemma majorant_mono_time {L s t : ℝ} (hL : 0 ≤ L) (hs : 0 ≤ s) (hst : s ≤ t)
    (n : ℕ) : majorant L s n ≤ majorant L t n := by
  unfold majorant
  gcongr

variable (w : ι → ℝ → ℝ) (b : ℝ → (ι → ℝ) → ι → ℝ)
  (hw : ∀ i, Continuous (w i))
  (hb : ∀ i, Measurable (fun p : ℝ × (ι → ℝ) => b p.1 p.2 i))
  (hbound : ∀ t y i, |b t y i| ≤ 1)
  {L : ℝ} (hL : 0 ≤ L)
  (hresponse : ∀ (s : ℝ) (y y' : ι → ℝ) (D : ℝ),
    0 ≤ D → (∀ j, |y j - y' j| ≤ D) →
    ∀ i, |b s y i - b s y' i| ≤ L * D)

include hw hb hbound hL hresponse

lemma uniformly_iterate_decode {T : ℝ} (hT : 0 ≤ T) :
    TendstoUniformly
      (fun n (p : ι × Icc (0 : ℝ) T) => iterate w b n p.1 p.2)
      (fun p => decode w b p.1 p.2) atTop ∧
    ∀ n (p : ι × Icc (0 : ℝ) T),
      dist (iterate w b n p.1 p.2) (decode w b p.1 p.2) ≤
        ∑' k, majorant L T (n + k) := by
  obtain ⟨z, hz, herror⟩ :=
    DeterministicDecoder.exists_uniform_limit_of_picard_increments
      (fun n (p : ι × Icc (0 : ℝ) T) => iterate w b n p.1 p.2) hL hT
      (fun n p => by
        have hinc := iterate_increment_le w b hw hb hbound hL hresponse n p.1 p.2 p.2.2.1
        have hmono := majorant_mono_time hL p.2.2.1 p.2.2.2 n
        simpa only [Real.dist_eq, abs_sub_comm, majorant,
          DeterministicDecoder.picardBound] using hinc.trans hmono)
  have heq : z = fun p => decode w b p.1 p.2 := by
    funext p
    exact (hz.tendsto_at p).limUnder_eq.symm
  subst z
  exact ⟨hz, herror⟩

lemma tendsto_iterate_decode (i : ι) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n => iterate w b n i t) atTop (𝓝 (decode w b i t)) := by
  exact (uniformly_iterate_decode w b hw hb hbound hL hresponse ht).1.tendsto_at
    (i, ⟨t, ht, le_rfl⟩)

lemma continuous_decode_compact (i : ι) {T : ℝ} (hT : 0 ≤ T) :
    Continuous (fun t : Icc (0 : ℝ) T => decode w b i t) := by
  have hu := (uniformly_iterate_decode w b hw hb hbound hL hresponse hT).1
  exact (hu.comp (fun t => (i, t))).continuous
    (Filter.Eventually.of_forall (fun n =>
      (continuous_iterate w b hw hb hbound n i).comp continuous_subtype_val)).frequently

lemma decode_integral_equation (i : ι) {t : ℝ} (ht : 0 ≤ t) :
    decode w b i t = w i t +
      ∫ s in (0 : ℝ)..t, b s (fun j => decode w b j s) i := by
  apply DeterministicDecoder.integral_equation_at_of_uniform_limit
    b w (iterate w b) (decode w b) hL ht
  · intro s x y D hD hxy j
    exact hresponse s x y D hD hxy j
  · exact hbound
  · exact measurable_drift_iterate w b hw hb hbound
  · exact (uniformly_iterate_decode w b hw hb hbound hL hresponse ht).1
  · intro n j
    rfl

omit hL hresponse in
lemma measurable_decode_time (i : ι) : Measurable (decode w b i) := by
  exact (StronglyMeasurable.limUnder (l := atTop)
    (fun n => (continuous_iterate w b hw hb hbound n i).measurable.stronglyMeasurable)).measurable

omit hL hresponse in
lemma measurable_drift_decode (i : ι) :
    Measurable (fun s => b s (fun j => decode w b j s) i) := by
  exact (hb i).comp (measurable_id.prodMk (Measurable.of_eval (fun j => measurable_decode_time w b hw hb hbound j)))

lemma continuousOn_decode (i : ι) : ContinuousOn (decode w b i) (Ici 0) := by
  have hc : Continuous (fun t => w i t +
      ∫ s in (0 : ℝ)..t, b s (fun j => decode w b j s) i) := by
    exact (hw i).add (intervalIntegral.continuous_primitive
      (intervalIntegrable_of_measurable_bounded
        (measurable_drift_decode w b hw hb hbound i) (fun s => hbound s _ i)) 0)
  apply hc.continuousOn.congr
  intro t ht
  exact decode_integral_equation w b hw hb hbound hL hresponse i ht

end Problem336.Picard

end

end OAI
