import OAI.Probability.SpanningForest.CanonicalDrift
import OAI.Probability.SpanningForest.PicardSolution

namespace OAI

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace Problem336.CanonicalDecoder

variable {α ι : Type*}

def drift (f : ℕ → α → ℝ → (ι → ℝ) → ι → ℝ)
    (a : α) (t : ℝ) (y : ι → ℝ) (i : ι) : ℝ :=
  CanonicalDrift.outerLimit (fun n (p : ℝ × (ι → ℝ)) => f n a p.1 p.2 i) (t, y)

lemma measurable_drift [MeasurableSpace α]
    (f : ℕ → α → ℝ → (ι → ℝ) → ι → ℝ)
    (hf : ∀ n i, Measurable
      (fun p : α × (ℝ × (ι → ℝ)) => f n p.1 p.2.1 p.2.2 i)) (i : ι) :
    Measurable (fun p : α × (ℝ × (ι → ℝ)) => drift f p.1 p.2.1 p.2.2 i) := by
  exact Measurable.limsup (fun n => hf n i)

lemma drift_mem_Icc
    (f : ℕ → α → ℝ → (ι → ℝ) → ι → ℝ)
    (hf : ∀ n a t y i, f n a t y i ∈ Icc (0 : ℝ) 1)
    (a : α) (t : ℝ) (y : ι → ℝ) (i : ι) :
    drift f a t y i ∈ Icc (0 : ℝ) 1 := by
  unfold drift
  exact CanonicalDrift.outerLimit_mem_Icc
    (b := fun n (p : ℝ × (ι → ℝ)) => f n a p.1 p.2 i)
    (fun n p => hf n a p.1 p.2 i) (t, y)

lemma abs_drift_le_one
    (f : ℕ → α → ℝ → (ι → ℝ) → ι → ℝ)
    (hf : ∀ n a t y i, f n a t y i ∈ Icc (0 : ℝ) 1)
    (a : α) (t : ℝ) (y : ι → ℝ) (i : ι) :
    |drift f a t y i| ≤ 1 := by
  have h := drift_mem_Icc f hf a t y i
  simpa only [abs_of_nonneg h.1] using h.2

lemma drift_response
    (f : ℕ → α → ℝ → (ι → ℝ) → ι → ℝ)
    (hf : ∀ n a t y i, f n a t y i ∈ Icc (0 : ℝ) 1)
    {L : ℝ}
    (hresponse : ∀ n a t y y' D, 0 ≤ D →
      (∀ j, |y j - y' j| ≤ D) → ∀ i,
      |f n a t y i - f n a t y' i| ≤ L * D)
    (a : α) (t : ℝ) (y y' : ι → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (hyy' : ∀ j, |y j - y' j| ≤ D) (i : ι) :
    |drift f a t y i - drift f a t y' i| ≤ L * D := by
  unfold drift
  exact CanonicalDrift.abs_outerLimit_sub_le
    (b := fun n (p : ℝ × (ι → ℝ)) => f n a p.1 p.2 i)
    (lo := 0) (hi := 1) (x := (t, y)) (y := (t, y'))
    (fun n p => hf n a p.1 p.2 i)
    (fun n => hresponse n a t y y' D hD hyy' i)

lemma drift_relabel
    {β κ : Type*} (e : ι ≃ κ) (a : α) (a' : β)
    (f : ℕ → α → ℝ → (ι → ℝ) → ι → ℝ)
    (g : ℕ → β → ℝ → (κ → ℝ) → κ → ℝ)
    (hfg : ∀ n t y i, g n a' t (fun k => y (e.symm k)) (e i) = f n a t y i)
    (t : ℝ) (y : ι → ℝ) (i : ι) :
    drift g a' t (fun k => y (e.symm k)) (e i) = drift f a t y i := by
  exact Filter.limsup_congr (Filter.Eventually.of_forall (fun n => hfg n t y i))

lemma measurable_decode [MeasurableSpace α]
    (f : ℕ → α → ℝ → (ι → ℝ) → ι → ℝ) (w : α → ι → ℝ → ℝ)
    (hf : ∀ n i, Measurable
      (fun p : α × (ℝ × (ι → ℝ)) => f n p.1 p.2.1 p.2.2 i))
    (hw : ∀ i, Measurable (fun p : α × ℝ => w p.1 i p.2)) (i : ι) :
    Measurable (fun p : α × ℝ => Picard.decode (w p.1) (drift f p.1) i p.2) :=
  Picard.measurable_decode w (drift f) hw (measurable_drift f hf) i

lemma decode_integral_equation [MeasurableSpace α]
    (f : ℕ → α → ℝ → (ι → ℝ) → ι → ℝ)
    (hf : ∀ n i, Measurable
      (fun p : α × (ℝ × (ι → ℝ)) => f n p.1 p.2.1 p.2.2 i))
    (hbound : ∀ n a t y i, f n a t y i ∈ Icc (0 : ℝ) 1)
    {L : ℝ} (hL : 0 ≤ L)
    (hresponse : ∀ n a t y y' D, 0 ≤ D →
      (∀ j, |y j - y' j| ≤ D) → ∀ i,
      |f n a t y i - f n a t y' i| ≤ L * D)
    (a : α) (w : ι → ℝ → ℝ) (hw : ∀ i, Continuous (w i))
    (i : ι) {t : ℝ} (ht : 0 ≤ t) :
    Picard.decode w (drift f a) i t = w i t +
      ∫ s in (0 : ℝ)..t, drift f a s (fun j => Picard.decode w (drift f a) j s) i := by
  have hp : Measurable (fun p : ℝ × (ι → ℝ) => (a, p)) :=
    measurable_const.prodMk measurable_id
  have hm : ∀ j, Measurable (fun p : ℝ × (ι → ℝ) => drift f a p.1 p.2 j) := by
    intro j
    change Measurable (fun p : ℝ × (ι → ℝ) =>
      Filter.limsup (fun n => f n a p.1 p.2 j) atTop)
    apply Measurable.limsup
    intro n
    exact (hf n j).comp hp
  exact Picard.decode_integral_equation w (drift f a) hw hm
    (abs_drift_le_one f hbound a) hL (drift_response f hbound hresponse a) i ht

lemma decode_relabel
    {β κ : Type*} (e : ι ≃ κ) (a : α) (a' : β)
    (f : ℕ → α → ℝ → (ι → ℝ) → ι → ℝ)
    (g : ℕ → β → ℝ → (κ → ℝ) → κ → ℝ)
    (hfg : ∀ n t y i, g n a' t (fun k => y (e.symm k)) (e i) = f n a t y i)
    (w : ι → ℝ → ℝ) (w' : κ → ℝ → ℝ)
    (hw : ∀ i t, w' (e i) t = w i t) (i : ι) (t : ℝ) :
    Picard.decode w' (drift g a') (e i) t = Picard.decode w (drift f a) i t := by
  exact Picard.decode_relabel e w w' (drift f a) (drift g a') hw
    (fun s y j => drift_relabel e a a' f g hfg s y j) i t

end Problem336.CanonicalDecoder

end

end OAI
