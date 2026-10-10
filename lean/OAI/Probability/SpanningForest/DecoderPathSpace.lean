import OAI.Probability.SpanningForest.PicardNonnegativeTime

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped Topology NNReal

namespace Problem336.DecoderPathSpace

lemma measurable_of_evaluations {α : Type*} [MeasurableSpace α]
    [MeasurableSpace C(ℝ≥0, ℝ)] [BorelSpace C(ℝ≥0, ℝ)]
    (F : α → C(ℝ≥0, ℝ))
    (hF : ∀ t, Measurable (fun a => F a t)) : Measurable F := by
  obtain ⟨S, hS, hd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  let : Countable S := hS.to_subtype
  let evalS : C(ℝ≥0, ℝ) → S → ℝ := fun p s => p s
  have hc : Continuous evalS := by
    apply continuous_pi
    intro s
    exact continuous_eval.comp (continuous_id.prodMk continuous_const)
  have hI : Function.Injective evalS := by
    intro p q hpq
    apply ContinuousMap.ext
    have hh : (p : ℝ≥0 → ℝ) = q :=
      Continuous.ext_on hd p.continuous q.continuous
        (fun t ht => congrFun hpq ⟨t, ht⟩)
    exact congrFun hh
  apply hc.measurableEmbedding hI |>.measurable_comp_iff.mp
  exact Measurable.of_eval (fun s => hF s)

variable {ι : Type*}

def decodedPath
    (w : ι → ℝ≥0 → ℝ) (b : ℝ → (ι → ℝ) → ι → ℝ)
    (hw : ∀ i, Continuous (w i))
    (hb : ∀ i, Measurable (fun p : ℝ × (ι → ℝ) => b p.1 p.2 i))
    (hbound : ∀ t y i, |b t y i| ≤ 1)
    {L : ℝ} (hL : 0 ≤ L)
    (hresponse : ∀ t y z D, 0 ≤ D → (∀ j, |y j - z j| ≤ D) →
      ∀ i, |b t y i - b t z i| ≤ L * D) (i : ι) : C(ℝ≥0, ℝ) :=
  ⟨Picard.NonnegativeTime.decodePath w b i,
    Picard.NonnegativeTime.continuous_decodePath w b hw hb hbound hL hresponse i⟩

lemma measurable_decodedPath
    {α : Type*} [MeasurableSpace α]
    [MeasurableSpace C(ℝ≥0, ℝ)] [BorelSpace C(ℝ≥0, ℝ)]
    (w : α → ι → ℝ≥0 → ℝ) (b : α → ℝ → (ι → ℝ) → ι → ℝ)
    (hw : ∀ a i, Continuous (w a i))
    (hwm : ∀ i, Measurable (fun p : α × ℝ≥0 => w p.1 i p.2))
    (hbm : ∀ i, Measurable
      (fun p : α × (ℝ × (ι → ℝ)) => b p.1 p.2.1 p.2.2 i))
    (hb : ∀ a i, Measurable (fun p : ℝ × (ι → ℝ) => b a p.1 p.2 i))
    (hbound : ∀ a t y i, |b a t y i| ≤ 1)
    {L : ℝ} (hL : 0 ≤ L)
    (hresponse : ∀ a t y z D, 0 ≤ D → (∀ j, |y j - z j| ≤ D) →
      ∀ i, |b a t y i - b a t z i| ≤ L * D) (i : ι) :
    Measurable (fun a => decodedPath (w a) (b a) (hw a) (hb a)
      (hbound a) hL (hresponse a) i) := by
  apply measurable_of_evaluations
  intro t
  have hm := Picard.NonnegativeTime.measurable_decodePath w b hwm hbm i
  exact hm.comp (measurable_id.prodMk measurable_const)

end Problem336.DecoderPathSpace

end

end OAI
