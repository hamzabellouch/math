import OAI.Probability.LatticePassage.ProductVariance
import Mathlib.MeasureTheory.Integral.Pi

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Finset

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]

lemma measurable_finCons (n : ℕ) :
    Measurable (fun z : α × (Fin n → α) => (Fin.cons z.1 z.2 : Fin (n+1) → α)) := by
  apply Measurable.of_eval
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using (measurable_fst : Measurable (Prod.fst : α × (Fin n → α) → α))
  · simpa only [Function.comp_def, Fin.cons_succ] using (measurable_pi_apply j).comp (measurable_snd :
      Measurable (Prod.snd : α × (Fin n → α) → (Fin n → α)))

lemma finCons_preserving (n : ℕ) :
    MeasurePreserving (fun z : α × (Fin n → α) => Fin.cons z.1 z.2)
      (μ.prod (Measure.pi (fun _ : Fin n => μ)))
      (Measure.pi (fun _ : Fin (n+1) => μ)) := by
  simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Fin.zero_succAbove, Equiv.coe_fn_mk, cast_eq] using
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0).symm

lemma integral_finCons {n : ℕ} {f : (Fin (n+1) → α) → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀ v, |f v| ≤ C) :
    (∫ v, f v ∂Measure.pi (fun _ : Fin (n+1) => μ)) =
      ∫ a, ∫ w, f (Fin.cons a w) ∂Measure.pi (fun _ : Fin n => μ) ∂μ := by
  have he := integral_map (finCons_preserving μ n).aemeasurable hf.aestronglyMeasurable
  rw [(finCons_preserving μ n).map_eq] at he
  rw [he]
  exact integral_prod _ ((bounded_memLp_two (hf.comp (measurable_finCons n))
    C (fun z => hC (Fin.cons z.1 z.2))).integrable (by norm_num))

noncomputable def coordinateVariance {ι : Type*} [DecidableEq ι]
    (f : (ι → α) → ℝ) (i : ι) (v : ι → α) : ℝ :=
  variance (fun u => f (Function.update v i u)) μ

lemma measurable_coordinateVariance {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → α) → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ v, |f v| ≤ C) (i : ι) :
    Measurable (coordinateVariance μ f i) := by
  apply measurable_section_variance (C := C) (f := fun z => f (Function.update z.1 i z.2))
  · exact hf.comp (by fun_prop)
  · exact fun z => hC _

lemma coordinateVariance_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → α) → ℝ} (hf : Measurable f) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ v, |f v| ≤ C) (i : ι) (v : ι → α) :
    |coordinateVariance μ f i v| ≤ C^2 := by
  rw [coordinateVariance, abs_of_nonneg (variance_nonneg _ _)]
  exact variance_le_bound_square (hf.comp (by fun_prop)) hC0 (fun _ => hC _)

lemma integrable_coordinateVariance {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → α) → ℝ} (hf : Measurable f) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ v, |f v| ≤ C) (i : ι) :
    Integrable (coordinateVariance μ f i) (Measure.pi (fun _ : ι => μ)) :=
  (bounded_memLp_two (measurable_coordinateVariance μ hf hC i) (C^2)
    (coordinateVariance_bound μ hf hC0 hC i)).integrable (by norm_num)

omit [IsProbabilityMeasure μ] in
lemma coordinateVariance_cons_zero {n : ℕ} (f : (Fin (n+1) → α) → ℝ)
    (a : α) (w : Fin n → α) :
    coordinateVariance μ f 0 (Fin.cons a w) = variance (fun u => f (Fin.cons u w)) μ := by
  simp only [coordinateVariance, Fin.update_cons_zero]

omit [IsProbabilityMeasure μ] in
lemma coordinateVariance_cons_succ {n : ℕ} (f : (Fin (n+1) → α) → ℝ)
    (i : Fin n) (a : α) (w : Fin n → α) :
    coordinateVariance μ f i.succ (Fin.cons a w) =
      coordinateVariance μ (fun v => f (Fin.cons a v)) i w := by
  simp only [coordinateVariance, ← Fin.cons_update]

lemma integral_coordinateVariance_zero {n : ℕ} {f : (Fin (n+1) → α) → ℝ}
    (hf : Measurable f) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ v, |f v| ≤ C) :
    (∫ v, coordinateVariance μ f 0 v ∂Measure.pi (fun _ : Fin (n+1) => μ)) =
      ∫ w, variance (fun u => f (Fin.cons u w)) μ ∂Measure.pi (fun _ : Fin n => μ) := by
  rw [integral_finCons μ (measurable_coordinateVariance μ hf hC 0)
    (coordinateVariance_bound μ hf hC0 hC 0)]
  simp [coordinateVariance_cons_zero]

lemma integral_coordinateVariance_succ {n : ℕ} {f : (Fin (n+1) → α) → ℝ}
    (hf : Measurable f) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ v, |f v| ≤ C) (i : Fin n) :
    (∫ v, coordinateVariance μ f i.succ v ∂Measure.pi (fun _ : Fin (n+1) => μ)) =
      ∫ a, ∫ w, coordinateVariance μ (fun v => f (Fin.cons a v)) i w
        ∂Measure.pi (fun _ : Fin n => μ) ∂μ := by
  rw [integral_finCons μ (measurable_coordinateVariance μ hf hC i.succ)
    (coordinateVariance_bound μ hf hC0 hC i.succ)]
  simp only [coordinateVariance_cons_succ]

theorem variance_fin_le_sum_coordinateVariance (n : ℕ)
    {f : (Fin n → α) → ℝ} (hf : Measurable f)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ v, |f v| ≤ C) :
    variance f (Measure.pi (fun _ : Fin n => μ)) ≤
      ∑ i : Fin n, ∫ v, coordinateVariance μ f i v ∂Measure.pi (fun _ : Fin n => μ) := by
  induction n with
  | zero =>
    have he : f = fun _ => f (fun i => Fin.elim0 i) := by
      funext v
      congr 1
      funext i
      exact Fin.elim0 i
    rw [he]
    simp [variance_eq_integral measurable_const.aemeasurable]
  | succ n ih =>
    let F := fun z : α × (Fin n → α) => f (Fin.cons z.1 z.2)
    have hFm : Measurable F := hf.comp (measurable_finCons n)
    have hFb : ∀ z, |F z| ≤ C := fun z => hC _
    have he : variance f (Measure.pi (fun _ : Fin (n+1) => μ)) =
        variance F (μ.prod (Measure.pi (fun _ : Fin n => μ))) := by
      rw [← (finCons_preserving μ n).map_eq,
        variance_map hf.aemeasurable (finCons_preserving μ n).aemeasurable]
      rfl
    rw [he]
    have hv := product_variance_le (μ := μ) (ν := Measure.pi (fun _ : Fin n => μ))
      hFm hC0 hFb
    apply hv.trans
    have hI : ∀ i : Fin n, Integrable (fun a => ∫ w,
        coordinateVariance μ (fun v => f (Fin.cons a v)) i w
        ∂Measure.pi (fun _ : Fin n => μ)) μ := by
      intro i
      have hm := (measurable_coordinateVariance μ hf hC i.succ).comp (measurable_finCons n)
      have hb := fun z : α × (Fin n → α) =>
        coordinateVariance_bound μ hf hC0 hC i.succ (Fin.cons z.1 z.2)
      have hi := (bounded_memLp_two (μ := μ.prod (Measure.pi (fun _ : Fin n => μ)))
        hm (C^2) hb).integrable (by norm_num)
      simpa only [Function.comp_def, coordinateVariance_cons_succ] using hi.integral_prod_left
    have hstep := integral_mono (integrable_section_variance hFm hC0 hFb)
      (integrable_finsetSum Finset.univ (fun i _ => hI i)) (fun a =>
        ih (hf.comp ((measurable_finCons n).comp (measurable_const.prodMk measurable_id)))
          (fun v => hC (Fin.cons a v)))
    rw [integral_finsetSum _ (fun i _ => hI i)] at hstep
    rw [Fin.sum_univ_succ, integral_coordinateVariance_zero μ hf hC0 hC]
    simp_rw [integral_coordinateVariance_succ μ hf hC0 hC]
    dsimp [F] at hstep ⊢
    linarith

lemma reindex_preserving {ι κ : Type*} [Fintype ι] [Fintype κ] (e : κ ≃ ι) :
    MeasurePreserving (fun v : κ → α => fun i => v (e.symm i))
      (Measure.pi (fun _ : κ => μ)) (Measure.pi (fun _ : ι => μ)) := by
  convert measurePreserving_piCongrLeft (fun _ : ι => μ) e using 1
  funext v i
  simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]

omit [IsProbabilityMeasure μ] in
lemma coordinateVariance_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : κ ≃ ι) (f : (ι → α) → ℝ) (j : κ) (v : κ → α) :
    coordinateVariance μ (fun w => f (fun i => w (e.symm i))) j v =
      coordinateVariance μ f (e j) (fun i => v (e.symm i)) := by
  unfold coordinateVariance
  congr 1
  funext u
  dsimp only
  congr 1
  funext i
  by_cases hi : i = e j
  · subst i
    simp
  · have hj : e.symm i ≠ j := by
      intro h
      apply hi
      simpa using congrArg e h
    simp [Function.update_of_ne hi, Function.update_of_ne hj]

theorem variance_pi_le_sum_coordinateVariance {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → α) → ℝ} (hf : Measurable f)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ v, |f v| ≤ C) :
    variance f (Measure.pi (fun _ : ι => μ)) ≤
      ∑ i : ι, ∫ v, coordinateVariance μ f i v ∂Measure.pi (fun _ : ι => μ) := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hmp := reindex_preserving μ e
  have hg := hf.comp hmp.measurable
  have ht := variance_fin_le_sum_coordinateVariance μ (Fintype.card ι) hg hC0
    (fun w => hC (fun i => w (e.symm i)))
  simp only [Function.comp_def] at ht
  rw [hmp.variance_fun_comp hf.aemeasurable] at ht
  simp only [coordinateVariance_reindex] at ht
  have he : ∀ j : Fin (Fintype.card ι),
      (∫ w, coordinateVariance μ f (e j) (fun i => w (e.symm i))
        ∂Measure.pi (fun _ : Fin (Fintype.card ι) => μ)) =
      ∫ v, coordinateVariance μ f (e j) v ∂Measure.pi (fun _ : ι => μ) := by
    intro j
    have h := integral_map hmp.aemeasurable
      (measurable_coordinateVariance μ hf hC (e j)).aestronglyMeasurable
    rw [hmp.map_eq] at h
    exact h.symm
  simp_rw [he] at ht
  rwa [e.sum_comp (fun i => ∫ v, coordinateVariance μ f i v ∂Measure.pi (fun _ : ι => μ))] at ht

end CompanionFPP

end OAI
