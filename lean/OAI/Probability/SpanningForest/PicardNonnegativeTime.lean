import OAI.Probability.SpanningForest.PicardSolution
import OAI.Probability.SpanningForest.PicardUniqueness

namespace OAI

noncomputable section

open Filter MeasureTheory
open scoped Topology NNReal

namespace Problem336.Picard.NonnegativeTime

variable {ι : Type*}

def extendInput (w : ι → ℝ≥0 → ℝ) (i : ι) (t : ℝ) : ℝ :=
  w i (Real.toNNReal t)

@[simp] theorem extendInput_coe (w : ι → ℝ≥0 → ℝ) (i : ι) (t : ℝ≥0) :
    extendInput w i (t : ℝ) = w i t := by
  simp only [extendInput, Real.toNNReal_coe]

def decodePath (w : ι → ℝ≥0 → ℝ) (b : ℝ → (ι → ℝ) → ι → ℝ)
    (i : ι) (t : ℝ≥0) : ℝ :=
  Picard.decode (extendInput w) b i t

theorem continuous_extendInput {w : ι → ℝ≥0 → ℝ}
    (hw : ∀ i, Continuous (w i)) (i : ι) : Continuous (extendInput w i) :=
  (hw i).comp continuous_real_toNNReal

theorem measurable_extendInput
    {α : Type*} [MeasurableSpace α] (w : α → ι → ℝ≥0 → ℝ)
    (hw : ∀ i, Measurable (fun p : α × ℝ≥0 => w p.1 i p.2))
    (i : ι) : Measurable (fun p : α × ℝ => extendInput (w p.1) i p.2) :=
  (hw i).comp (measurable_fst.prodMk
    (continuous_real_toNNReal.measurable.comp measurable_snd))

theorem measurable_decodePath
    {α : Type*} [MeasurableSpace α]
    (w : α → ι → ℝ≥0 → ℝ) (b : α → ℝ → (ι → ℝ) → ι → ℝ)
    (hw : ∀ i, Measurable (fun p : α × ℝ≥0 => w p.1 i p.2))
    (hb : ∀ i, Measurable
      (fun p : α × (ℝ × (ι → ℝ)) => b p.1 p.2.1 p.2.2 i)) (i : ι) :
    Measurable (fun p : α × ℝ≥0 => decodePath (w p.1) (b p.1) i p.2) := by
  change Measurable (fun p : α × ℝ≥0 =>
    Picard.decode (extendInput (w p.1)) (b p.1) i (p.2 : ℝ))
  have hm : Measurable (fun p : α × ℝ =>
      Picard.decode (extendInput (w p.1)) (b p.1) i p.2) :=
    @Picard.measurable_decode ι α _ (fun a => extendInput (w a)) b
      (measurable_extendInput w hw) hb i
  have hc : Measurable (fun p : α × ℝ≥0 => (p.1, (p.2 : ℝ))) :=
    measurable_fst.prodMk measurable_snd.subtype_coe
  convert hm.comp hc using 1
  rfl

section Solution

variable (w : ι → ℝ≥0 → ℝ) (b : ℝ → (ι → ℝ) → ι → ℝ)
  (hw : ∀ i, Continuous (w i))
  (hb : ∀ i, Measurable (fun p : ℝ × (ι → ℝ) => b p.1 p.2 i))
  (hbound : ∀ t y i, |b t y i| ≤ 1)
  {L : ℝ} (hL : 0 ≤ L)
  (hresponse : ∀ t y z D, 0 ≤ D → (∀ j, |y j - z j| ≤ D) →
    ∀ i, |b t y i - b t z i| ≤ L * D)

include hw hb hbound hL hresponse

theorem continuous_decodePath (i : ι) : Continuous (decodePath w b i) := by
  exact (Picard.continuousOn_decode (extendInput w) b
    (continuous_extendInput hw) hb hbound hL hresponse i).comp_continuous
      NNReal.continuous_coe (fun t => t.2)

theorem decodePath_integral_equation (i : ι) (t : ℝ≥0) :
    decodePath w b i t = w i t +
      ∫ s in (0 : ℝ)..(t : ℝ), b s (fun j => decodePath w b j (Real.toNNReal s)) i := by
  change Picard.decode (extendInput w) b i (t : ℝ) = _
  calc
    Picard.decode (extendInput w) b i (t : ℝ) =
        extendInput w i (t : ℝ) + ∫ s in (0 : ℝ)..(t : ℝ),
          b s (fun j => Picard.decode (extendInput w) b j s) i :=
      Picard.decode_integral_equation (extendInput w) b
        (continuous_extendInput hw) hb hbound hL hresponse i (t := (t : ℝ)) t.2
    _ = _ := by
      rw [extendInput_coe]
      congr 1
      apply intervalIntegral.integral_congr
      intro s hs
      have hst : (0 : ℝ) ≤ (t : ℝ) := t.2
      have hs0 : 0 ≤ s := by
        simpa only [min_eq_left hst] using hs.1
      have hfield : (fun j => Picard.decode (extendInput w) b j s) =
          (fun j => decodePath w b j (Real.toNNReal s)) := by
        funext j
        simp only [decodePath, Real.coe_toNNReal s hs0]
      exact congrArg (fun y => b s y i) hfield

theorem decodePath_zero (i : ι) : decodePath w b i 0 = w i 0 := by
  simpa using decodePath_integral_equation w b hw hb hbound hL hresponse i 0

end Solution

theorem decodePath_relabel
    {κ : Type*} (e : ι ≃ κ)
    (w : ι → ℝ≥0 → ℝ) (w' : κ → ℝ≥0 → ℝ)
    (b : ℝ → (ι → ℝ) → ι → ℝ) (b' : ℝ → (κ → ℝ) → κ → ℝ)
    (hw : ∀ i t, w' (e i) t = w i t)
    (hb : ∀ t (y : ι → ℝ) i,
      b' t (fun k => y (e.symm k)) (e i) = b t y i)
    (i : ι) (t : ℝ≥0) : decodePath w' b' (e i) t = decodePath w b i t := by
  exact Picard.decode_relabel e (extendInput w) (extendInput w') b b'
    (fun j s => hw j (Real.toNNReal s)) hb i t

theorem decodePath_causal
    (w v : ι → ℝ≥0 → ℝ) (b : ℝ → (ι → ℝ) → ι → ℝ) (T : ℝ≥0)
    (hw : ∀ i t, t ≤ T → w i t = v i t)
    (i : ι) (t : ℝ≥0) (ht : t ≤ T) :
    decodePath w b i t = decodePath v b i t := by
  apply Picard.decode_causal (extendInput w) (extendInput v) b (T : ℝ) _ i
    (t : ℝ) ⟨t.2, ht⟩
  intro j s hs
  apply hw j (Real.toNNReal s)
  change (Real.toNNReal s : ℝ) ≤ (T : ℝ)
  simpa only [Real.coe_toNNReal s hs.1] using hs.2

theorem decodePath_eq_solution
    (w x : ι → ℝ≥0 → ℝ) (b : ℝ → (ι → ℝ) → ι → ℝ)
    (hw : ∀ i, Continuous (w i)) (hx : ∀ i, Measurable (x i))
    (hb : ∀ i, Measurable (fun p : ℝ × (ι → ℝ) => b p.1 p.2 i))
    (hbound : ∀ t y i, |b t y i| ≤ 1)
    {L : ℝ} (hL : 0 ≤ L)
    (hresponse : ∀ t y z D, 0 ≤ D → (∀ j, |y j - z j| ≤ D) →
      ∀ i, |b t y i - b t z i| ≤ L * D)
    (hsol : ∀ (t : ℝ≥0) i, x i t = w i t +
      ∫ s in (0 : ℝ)..(t : ℝ), b s (fun j => x j (Real.toNNReal s)) i)
    (i : ι) (t : ℝ≥0) : decodePath w b i t = x i t := by
  have hsol' : ∀ s : ℝ, 0 ≤ s → ∀ j,
      extendInput x j s = extendInput w j s +
        ∫ r in (0 : ℝ)..s, b r (fun k => extendInput x k r) j := by
    intro s hs j
    simpa only [extendInput, Real.coe_toNNReal s hs] using hsol (Real.toNNReal s) j
  have heq := Picard.decode_eq_solution (extendInput w) (extendInput x) b
    (continuous_extendInput hw)
    (fun j => (hx j).comp continuous_real_toNNReal.measurable)
    hb hbound hL hresponse hsol' i (t : ℝ) t.2
  simpa only [decodePath, extendInput_coe] using heq

end Problem336.Picard.NonnegativeTime

end

end OAI
