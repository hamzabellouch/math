import Mathlib

namespace OAI

noncomputable section

open Filter MeasureTheory Set
open scoped Topology BigOperators

namespace Problem336.Picard

variable {ι : Type*}

def iterate (w : ι → ℝ → ℝ) (b : ℝ → (ι → ℝ) → ι → ℝ) :
    ℕ → ι → ℝ → ℝ
  | 0 => w
  | n + 1 => fun i t => w i t +
      ∫ s in (0 : ℝ)..t, b s (fun j => iterate w b n j s) i

def majorant (L T : ℝ) (n : ℕ) : ℝ :=
  L ^ n * T ^ (n + 1) / (n + 1).factorial

lemma intervalIntegrable_of_measurable_bounded
    {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ t, |f t| ≤ C)
    (a d : ℝ) : IntervalIntegrable f volume a d := by
  constructor
  · apply Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne hf.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun t => by simpa [Real.norm_eq_abs] using hC t
  · apply Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne hf.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun t => by simpa [Real.norm_eq_abs] using hC t

lemma continuous_iterate
    (w : ι → ℝ → ℝ) (b : ℝ → (ι → ℝ) → ι → ℝ)
    (hw : ∀ i, Continuous (w i))
    (hb : ∀ i, Measurable (fun p : ℝ × (ι → ℝ) => b p.1 p.2 i))
    (hbound : ∀ t y i, |b t y i| ≤ 1) :
    ∀ n i, Continuous (iterate w b n i) := by
  intro n
  induction n with
  | zero => exact hw
  | succ n ih =>
    intro i
    have hm : Measurable (fun s => b s (fun j => iterate w b n j s) i) := by
      exact (hb i).comp (measurable_id.prodMk (Measurable.of_eval (fun j => (ih j).measurable)))
    exact (hw i).add (intervalIntegral.continuous_primitive
      (intervalIntegrable_of_measurable_bounded hm (fun s => hbound s _ i)) 0)

lemma majorant_nonneg {L t : ℝ} (hL : 0 ≤ L) (ht : 0 ≤ t) (n : ℕ) :
    0 ≤ majorant L t n := by
  unfold majorant
  positivity

lemma continuous_majorant (L : ℝ) (n : ℕ) : Continuous (fun t => majorant L t n) := by
  unfold majorant
  fun_prop

lemma integral_majorant (L t : ℝ) (n : ℕ) :
    (∫ s in (0 : ℝ)..t, L * majorant L s n) = majorant L t (n + 1) := by
  have heq : (fun s : ℝ => L * majorant L s n) =
      (fun s : ℝ => (L ^ (n + 1) / (n + 1).factorial) * s ^ (n + 1)) := by
    funext s
    simp only [majorant, pow_succ]
    ring
  rw [heq, intervalIntegral.integral_const_mul, integral_pow]
  simp only [zero_pow (by omega : n + 1 + 1 ≠ 0), sub_zero, majorant]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp

lemma measurable_drift_iterate
    (w : ι → ℝ → ℝ) (b : ℝ → (ι → ℝ) → ι → ℝ)
    (hw : ∀ i, Continuous (w i))
    (hb : ∀ i, Measurable (fun p : ℝ × (ι → ℝ) => b p.1 p.2 i))
    (hbound : ∀ t y i, |b t y i| ≤ 1) (n : ℕ) (i : ι) :
    Measurable (fun s => b s (fun j => iterate w b n j s) i) := by
  exact (hb i).comp (measurable_id.prodMk (Measurable.of_eval (fun j => (continuous_iterate w b hw hb hbound n j).measurable)))

lemma intervalIntegrable_drift_iterate
    (w : ι → ℝ → ℝ) (b : ℝ → (ι → ℝ) → ι → ℝ)
    (hw : ∀ i, Continuous (w i))
    (hb : ∀ i, Measurable (fun p : ℝ × (ι → ℝ) => b p.1 p.2 i))
    (hbound : ∀ t y i, |b t y i| ≤ 1) (n : ℕ) (i : ι) (a d : ℝ) :
    IntervalIntegrable (fun s => b s (fun j => iterate w b n j s) i) volume a d := by
  exact intervalIntegrable_of_measurable_bounded
    (measurable_drift_iterate w b hw hb hbound n i) (fun s => hbound s _ i) a d

lemma iterate_increment_le
    (w : ι → ℝ → ℝ) (b : ℝ → (ι → ℝ) → ι → ℝ)
    (hw : ∀ i, Continuous (w i))
    (hb : ∀ i, Measurable (fun p : ℝ × (ι → ℝ) => b p.1 p.2 i))
    (hbound : ∀ t y i, |b t y i| ≤ 1)
    {L : ℝ} (hL : 0 ≤ L)
    (hresponse : ∀ (s : ℝ) (y y' : ι → ℝ) (D : ℝ),
      0 ≤ D → (∀ j, |y j - y' j| ≤ D) →
      ∀ i, |b s y i - b s y' i| ≤ L * D) :
    ∀ n i t, 0 ≤ t →
      |iterate w b (n + 1) i t - iterate w b n i t| ≤ majorant L t n := by
  intro n
  induction n with
  | zero =>
    intro i t ht
    simp only [iterate, add_sub_cancel_left, majorant, pow_zero, zero_add,
      pow_one, Nat.factorial_one, Nat.cast_one, div_one, one_mul]
    have hh := intervalIntegral.norm_integral_le_of_norm_le (f :=
      fun s => b s (fun j => w j s) i) (g := fun _ => (1 : ℝ)) (μ := volume) ht
      (Filter.Eventually.of_forall fun s _ => by simpa [Real.norm_eq_abs] using hbound s _ i)
      (intervalIntegrable_const)
    simpa [Real.norm_eq_abs] using hh
  | succ n ih =>
    intro i t ht
    have hn := intervalIntegrable_drift_iterate w b hw hb hbound n i 0 t
    have hn1 := intervalIntegrable_drift_iterate w b hw hb hbound (n + 1) i 0 t
    have hid : iterate w b (n + 1 + 1) i t - iterate w b (n + 1) i t =
        ∫ s in (0 : ℝ)..t,
          (b s (fun j => iterate w b (n + 1) j s) i -
           b s (fun j => iterate w b n j s) i) := by
      rw [intervalIntegral.integral_sub hn1 hn]
      simp only [iterate]
      ring
    rw [hid]
    have hh := intervalIntegral.norm_integral_le_of_norm_le (f :=
      fun s => b s (fun j => iterate w b (n + 1) j s) i -
        b s (fun j => iterate w b n j s) i)
      (g := fun s => L * majorant L s n) (μ := volume) ht
      (Filter.Eventually.of_forall fun s hs => by
        rw [Real.norm_eq_abs]
        exact hresponse s _ _ _ (majorant_nonneg hL hs.1.le n)
          (fun j => ih j s hs.1.le) i)
      ((continuous_const.mul (continuous_majorant L n)).intervalIntegrable 0 t)
    simpa only [Real.norm_eq_abs, integral_majorant] using hh

lemma measurable_parametric_intervalIntegral
    {α : Type*} [MeasurableSpace α] (f : α → ℝ → ℝ)
    (hf : Measurable (Function.uncurry f)) (a d : α → ℝ)
    (ha : Measurable a) (hd : Measurable d) :
    Measurable (fun x => ∫ s in a x..d x, f x s) := by
  classical
  have hi (a d : α → ℝ) (ha : Measurable a) (hd : Measurable d) :
      Measurable (fun x => ∫ s in Ioc (a x) (d x), f x s) := by
    have hm : Measurable (fun q : α × ℝ =>
        if a q.1 < q.2 ∧ q.2 ≤ d q.1 then f q.1 q.2 else 0) := by
      exact Measurable.ite
        ((measurableSet_lt (ha.comp measurable_fst) measurable_snd).inter
          (measurableSet_le measurable_snd (hd.comp measurable_fst))) hf measurable_const
    have hh := hm.stronglyMeasurable.integral_prod_right' (ν := volume)
    convert hh.measurable using 1
    funext x
    rw [← integral_indicator measurableSet_Ioc]
    simp only [Set.indicator, Set.mem_Ioc]
  exact (hi a d ha hd).sub (hi d a hd ha)

lemma measurable_iterate
    {α : Type*} [MeasurableSpace α]
    (w : α → ι → ℝ → ℝ) (b : α → ℝ → (ι → ℝ) → ι → ℝ)
    (hw : ∀ i, Measurable (fun p : α × ℝ => w p.1 i p.2))
    (hb : ∀ i, Measurable
      (fun p : α × (ℝ × (ι → ℝ)) => b p.1 p.2.1 p.2.2 i)) :
    ∀ n i, Measurable (fun p : α × ℝ => iterate (w p.1) (b p.1) n i p.2) := by
  intro n
  induction n with
  | zero => exact hw
  | succ n ih =>
    intro i
    apply (hw i).add
    apply measurable_parametric_intervalIntegral
      (fun p : α × ℝ => fun s => b p.1 s
        (fun j => iterate (w p.1) (b p.1) n j s) i)
      _ (fun _ => 0) Prod.snd measurable_const measurable_snd
    exact (hb i).comp (measurable_fst.fst.prodMk
      (measurable_snd.prodMk (Measurable.of_eval (fun j =>
        (ih j).comp (measurable_fst.fst.prodMk measurable_snd)))))

def decode (w : ι → ℝ → ℝ) (b : ℝ → (ι → ℝ) → ι → ℝ) (i : ι) (t : ℝ) : ℝ :=
  Filter.limUnder atTop (fun n => iterate w b n i t)

lemma measurable_decode
    {α : Type*} [MeasurableSpace α]
    (w : α → ι → ℝ → ℝ) (b : α → ℝ → (ι → ℝ) → ι → ℝ)
    (hw : ∀ i, Measurable (fun p : α × ℝ => w p.1 i p.2))
    (hb : ∀ i, Measurable
      (fun p : α × (ℝ × (ι → ℝ)) => b p.1 p.2.1 p.2.2 i)) (i : ι) :
    Measurable (fun p : α × ℝ => decode (w p.1) (b p.1) i p.2) := by
  exact (StronglyMeasurable.limUnder (l := atTop)
    (fun n => (measurable_iterate w b hw hb n i).stronglyMeasurable)).measurable

lemma iterate_relabel
    {κ : Type*} (e : ι ≃ κ)
    (w : ι → ℝ → ℝ) (w' : κ → ℝ → ℝ)
    (b : ℝ → (ι → ℝ) → ι → ℝ) (b' : ℝ → (κ → ℝ) → κ → ℝ)
    (hw : ∀ i t, w' (e i) t = w i t)
    (hb : ∀ t (y : ι → ℝ) i,
      b' t (fun k => y (e.symm k)) (e i) = b t y i) :
    ∀ n i t, iterate w' b' n (e i) t = iterate w b n i t := by
  intro n
  induction n with
  | zero => exact hw
  | succ n ih =>
    intro i t
    simp only [iterate, hw]
    congr 1
    apply congrArg (fun f : ℝ → ℝ => ∫ s in (0 : ℝ)..t, f s)
    funext s
    have hfield : (fun k => iterate w' b' n k s) =
        (fun k => iterate w b n (e.symm k) s) := by
      funext k
      simpa using ih (e.symm k) s
    rw [hfield]
    exact hb s (fun j => iterate w b n j s) i

lemma decode_relabel
    {κ : Type*} (e : ι ≃ κ)
    (w : ι → ℝ → ℝ) (w' : κ → ℝ → ℝ)
    (b : ℝ → (ι → ℝ) → ι → ℝ) (b' : ℝ → (κ → ℝ) → κ → ℝ)
    (hw : ∀ i t, w' (e i) t = w i t)
    (hb : ∀ t (y : ι → ℝ) i,
      b' t (fun k => y (e.symm k)) (e i) = b t y i) (i : ι) (t : ℝ) :
    decode w' b' (e i) t = decode w b i t := by
  unfold decode
  congr 1
  funext n
  exact iterate_relabel e w w' b b' hw hb n i t

lemma iterate_causal
    (w v : ι → ℝ → ℝ) (b : ℝ → (ι → ℝ) → ι → ℝ) (T : ℝ)
    (hw : ∀ i t, t ∈ Icc 0 T → w i t = v i t) :
    ∀ n i t, t ∈ Icc 0 T → iterate w b n i t = iterate v b n i t := by
  intro n
  induction n with
  | zero => exact hw
  | succ n ih =>
    intro i t ht
    simp only [iterate, hw i t ht]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    have hfield : (fun j => iterate w b n j s) =
        (fun j => iterate v b n j s) := by
      funext j
      exact ih j s ⟨hs.1, hs.2.trans ht.2⟩
    exact congrArg (fun y => b s y i) hfield

lemma decode_causal
    (w v : ι → ℝ → ℝ) (b : ℝ → (ι → ℝ) → ι → ℝ) (T : ℝ)
    (hw : ∀ i t, t ∈ Icc 0 T → w i t = v i t)
    (i : ι) (t : ℝ) (ht : t ∈ Icc 0 T) :
    decode w b i t = decode v b i t := by
  unfold decode
  congr 1
  funext n
  exact iterate_causal w v b T hw n i t ht

end Problem336.Picard

end

end OAI
