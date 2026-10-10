import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.Delta
import OAI.Probability.CriticalPercolation.ProductMeasure.BitMeasure

namespace OAI

section
section CurrentModule0

noncomputable section
open Set
open scoped BigOperators Classical

namespace CriticalPercolation.Sharpness
open FiniteProduct

variable {E A : Type*} [Fintype E]

def weight (p : ℝ) (b : Prop) : ℝ := if b then p else 1 - p

lemma weight_sum (p : ℝ) : ∑ b, weight p b = 1 := by
  simp [weight]

lemma weight_nonneg {p : ℝ} (hp : p ∈ Icc 0 1) (b : Prop) :
    0 ≤ weight p b := by
  by_cases h : b <;> simp [weight, h, hp.1, hp.2]

lemma weight_eq_bitWeight (p : unitInterval) :
    weight (p : ℝ) = BernoulliProduct.bitWeight p := rfl

lemma hasDerivAt_weight (p : ℝ) (b : Prop) :
    HasDerivAt (fun q => weight q b) (if b then 1 else -1) p := by
  by_cases hb : b
  · convert hasDerivAt_id' p using 1 <;> first | rfl | simp [weight, hb]
  · convert (hasDerivAt_const p (1 : ℝ)).sub (hasDerivAt_id' p) using 1 <;>
      first | rfl | (simp only [weight, ite_eq_right hb]; first | rfl | norm_num)

lemma hasDerivAt_density (p : ℝ) (ω : E → Prop) :
    HasDerivAt (fun q => density (fun _ : E => weight q) ω)
      (∑ e, (∏ j ∈ Finset.univ.erase e, weight p (ω j)) *
        (if ω e then 1 else -1)) p := by
  simpa only [density, smul_eq_mul] using
    HasDerivAt.fun_finsetProd (u := Finset.univ)
      (fun (e : E) _ => hasDerivAt_weight p (ω e))

lemma density_score {p : ℝ} (hp : p ∈ Ioo 0 1) (ω : E → Prop) (e : E) :
    (∏ j ∈ Finset.univ.erase e, weight p (ω j)) * (if ω e then 1 else -1) =
      density (fun _ : E => weight p) ω *
        (if ω e then p⁻¹ else -(1-p)⁻¹) := by
  unfold density
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ e)]
  have hp0 : p ≠ 0 := hp.1.ne'
  have hp1 : 1-p ≠ 0 := (sub_pos.mpr hp.2).ne'
  by_cases he : ω e <;> simp [weight, he, hp0, hp1]

lemma hasDerivAt_expect_score {p : ℝ} (hp : p ∈ Ioo 0 1) (f : (E → Prop) → ℝ) :
    HasDerivAt (fun q => expect (fun _ : E => weight q) f)
      (∑ e, expect (fun _ : E => weight p)
        (fun ω => (if ω e then p⁻¹ else -(1-p)⁻¹) * f ω)) p := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ)
    (fun (ω : E → Prop) _ => (hasDerivAt_density p ω).mul_const (f ω))
  convert hd using 1 <;> try rfl
  simp only [expect, Finset.sum_mul, density_score hp]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  apply Finset.sum_congr rfl
  intro e _
  ring

lemma expect_eval_indicator [Fintype A] (w : E → A → ℝ)
    (hw : ∀ e, ∑ a, w e a = 1) (e : E) (b : A) :
    expect w (fun ω => if ω e = b then 1 else 0) = w e b := by
  have hi (ω : E → A) : (if ω e = b then (1:ℝ) else 0) =
      ∏ j, (if j = e then if ω j = b then 1 else 0 else 1) := by simp
  simp only [expect, hi, density, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun j a => w j a * (if j = e then if a = b then 1 else 0 else 1))]
  have hs (j : E) :
      (∑ a, w j a * (if j = e then if a = b then 1 else 0 else 1)) =
        if j = e then w e b else 1 := by
    split_ifs with he
    · subst j; simp
    · simp [hw]
  simp only [hs]
  simp

lemma expect_coordinate_mask [Fintype A] (w : E → A → ℝ)
    (hw : ∀ e, ∑ a, w e a = 1) (e : E) (b : A) (f : (E → A) → ℝ) :
    expect w (fun ω => if ω e = b then f ω else 0) =
      w e b * expect w (fun ω => f (Function.update ω e b)) := by
  have hid : (fun ω => if ω e = b then f ω else 0) =
      (fun ω => (if ω e = b then (1:ℝ) else 0)*f (Function.update ω e b)) := by
    funext ω
    split_ifs with h
    · have hu : Function.update ω e b = ω := by
        rw [← h]; exact Function.update_eq_self _ _
      simp [hu]
    · simp
  rw [hid]
  have hI : DependsOn (fun ω : E → A => if ω e = b then (1:ℝ) else 0) ({e} : Set E) := by
    intro ω ω' heq
    dsimp only
    rw [heq e (Set.mem_singleton e)]
  have hF : DependsOn (fun ω => f (Function.update ω e b)) ({e} : Set E)ᶜ := by
    intro ω ω' heq
    change f (Function.update ω e b) = f (Function.update ω' e b)
    congr 1
    funext j
    by_cases hj : j = e
    · subst j; simp
    · simp only [Function.update_of_ne hj]
      exact heq j hj
  rw [expect_indep w hw _ hI hF]
  congr 1
  exact expect_eval_indicator w hw e b

lemma score_eq_difference {p : ℝ} (hp : p ∈ Ioo 0 1) (e : E) (f : (E → Prop) → ℝ) :
    expect (fun _ : E => weight p)
      (fun ω => (if ω e then p⁻¹ else -(1-p)⁻¹) * f ω) =
    expect (fun _ : E => weight p) (fun ω => f (Function.update ω e True)) -
      expect (fun _ : E => weight p) (fun ω => f (Function.update ω e False)) := by
  have he : (fun ω => (if ω e then p⁻¹ else -(1-p)⁻¹) * f ω) =
      (fun ω => (if ω e = True then f ω else 0) * p⁻¹ -
        (if ω e = False then f ω else 0) * (1-p)⁻¹) := by
    funext ω
    by_cases h : ω e <;> simp [h, mul_comm]
  rw [he, expect_sub, expect_mul_const, expect_mul_const]
  have h1 : expect (fun _ : E => weight p)
      (fun ω => if ω e = True then f ω else 0) =
      p * expect (fun _ : E => weight p) (fun ω => f (Function.update ω e True)) := by
    convert expect_coordinate_mask (fun _ : E => weight p) (fun _ => weight_sum p) e True f using 1 <;>
      first | (congr 1; funext ω; split_ifs <;> rfl) | simp [weight]
  have h0 : expect (fun _ : E => weight p)
      (fun ω => if ω e = False then f ω else 0) =
      (1-p) * expect (fun _ : E => weight p) (fun ω => f (Function.update ω e False)) := by
    convert expect_coordinate_mask (fun _ : E => weight p) (fun _ => weight_sum p) e False f using 1 <;>
      first | (congr 1; funext ω; split_ifs <;> rfl) | simp [weight]
  rw [h1, h0]
  have hp0 := hp.1.ne'
  have hp1 := (sub_pos.mpr hp.2).ne'
  field_simp

theorem hasDerivAt_expect {p : ℝ} (hp : p ∈ Ioo 0 1) (f : (E → Prop) → ℝ) :
    HasDerivAt (fun q => expect (fun _ : E => weight q) f)
      (∑ e, expect (fun _ : E => weight p)
        (fun ω => f (Function.update ω e True) - f (Function.update ω e False))) p := by
  have hd := hasDerivAt_expect_score hp f
  simpa only [score_eq_difference hp, expect_sub] using hd

def probability (p : ℝ) (F : Set E → Prop) : ℝ :=
  expect (fun _ : E => weight p) (fun ω => if F ω then 1 else 0)

def closedPivot (F : Set E → Prop) (e : E) (ω : E → Prop) : Prop :=
  ¬ω e ∧ ¬F ω ∧ F (Function.update ω e True)

def pivotal (F : Set E → Prop) (e : E) (ω : Set E) : Prop :=
  F (Function.update ω e True) ∧ ¬ F (Function.update ω e False)

omit [Fintype E] in
lemma force_false_subset_true (ω : Set E) (e : E) :
    Set.Subset (Function.update ω e False) (Function.update ω e True) := by
  intro j hj
  change Function.update ω e True j
  change Function.update ω e False j at hj
  by_cases h : j=e
  · subst j; exact of_eq_true (Function.update_self e True ω)
  · erw [Function.update_of_ne h] at hj ⊢
    exact hj

omit [Fintype E] in
lemma indicator_difference (F : Set E → Prop)
    (hF : ∀ s t, s ⊆ t → F s → F t) (e : E) (ω : Set E) :
    (if F (Function.update ω e True) then (1:ℝ) else 0) -
        (if F (Function.update ω e False) then 1 else 0) =
      if pivotal F e ω then 1 else 0 := by
  have hm := hF _ _ (force_false_subset_true ω e)
  by_cases h1 : F (Function.update ω e True) <;>
    by_cases h0 : F (Function.update ω e False) <;> simp_all [pivotal]

theorem hasDerivAt_probability {p : ℝ} (hp : p ∈ Ioo 0 1)
    (F : Set E → Prop) (hF : ∀ s t, s ⊆ t → F s → F t) :
    HasDerivAt (fun q => probability q F) (∑ e, probability p (pivotal F e)) p := by
  have hd := hasDerivAt_expect hp (fun ω => if F ω then (1:ℝ) else 0)
  convert hd using 1 <;> try rfl
  apply Finset.sum_congr rfl
  intro e _
  unfold probability
  congr 1
  funext ω
  exact (indicator_difference F hF e ω).symm

omit [Fintype E] in
lemma closedPivot_iff (F : Set E → Prop) (e : E) (ω : Set E) :
    closedPivot F e ω ↔ ω e = False ∧ pivotal F e ω := by
  have hh : ¬ω e → Function.update ω e False = ω := by
    intro h
    have he : ω e = False := propext (iff_false_intro h)
    rw [← he]
    exact Function.update_eq_self _ _
  by_cases h : ω e
  · simp [closedPivot, h]
  · simp [closedPivot, pivotal, h, hh h, and_comm]

lemma probability_closedPivot (p : ℝ) (F : Set E → Prop) (e : E) :
    probability p (closedPivot F e) = (1-p) * probability p (pivotal F e) := by
  have he : (fun ω : E → Prop => if closedPivot F e ω then (1:ℝ) else 0) =
      (fun ω => if ω e = False then (if pivotal F e ω then 1 else 0) else 0) := by
    funext ω
    erw [closedPivot_iff]
    split_ifs <;> tauto
  unfold probability
  rw [he]
  have hm : expect (fun _ : E => weight p)
      (fun ω => if ω e = False then (if pivotal F e ω then 1 else 0) else 0) =
      (1-p)*expect (fun _ : E => weight p)
        (fun ω => if pivotal F e (Function.update ω e False) then 1 else 0) := by
    convert expect_coordinate_mask (fun _ : E => weight p) (fun _ => weight_sum p)
      e False (fun ω => if pivotal F e ω then 1 else 0) using 1 <;>
      first | (congr 1; funext ω; split_ifs <;> rfl) | simp [weight]
  calc
    _ = (1-p)*expect (fun _ : E => weight p)
        (fun ω => if pivotal F e (Function.update ω e False) then 1 else 0) := by
      convert hm using 1
      congr 1
    _ = _ := by
      congr 1
      congr 1
      funext ω
      simp only [pivotal, Function.update_idem]
      congr 1

theorem hasDerivAt_probability_closedPivot {p : ℝ} (hp : p ∈ Ioo 0 1)
    (F : Set E → Prop) (hF : ∀ s t, s ⊆ t → F s → F t) :
    HasDerivAt (fun q => probability q F)
      ((∑ e, probability p (closedPivot F e)) / (1-p)) p := by
  have hd := hasDerivAt_probability hp F hF
  convert hd using 1
  simp only [probability_closedPivot, ← Finset.mul_sum]
  exact mul_div_cancel_left₀ _ (sub_pos.mpr hp.2).ne'

lemma probability_nonneg {p : ℝ} (hp : p ∈ Icc 0 1) (F : Set E → Prop) :
    0 ≤ probability p F := by
  have h := expect_mono (w := fun _ : E => weight p)
    (fun _ b => weight_nonneg hp b)
    (f := fun _ => 0) (g := fun ω => if F ω then 1 else 0)
    (fun _ => by split_ifs <;> norm_num)
  simpa only [expect_const _ (fun _ => weight_sum p) 0, probability] using h

lemma probability_le_one {p : ℝ} (hp : p ∈ Icc 0 1) (F : Set E → Prop) :
    probability p F ≤ 1 := by
  have h := expect_mono (w := fun _ : E => weight p)
    (fun _ b => weight_nonneg hp b)
    (f := fun ω => if F ω then 1 else 0) (g := fun _ => 1)
    (fun _ => by split_ifs <;> norm_num)
  simpa only [expect_const _ (fun _ => weight_sum p) 1, probability] using h

end CriticalPercolation.Sharpness
end
end CurrentModule0

end

end OAI
