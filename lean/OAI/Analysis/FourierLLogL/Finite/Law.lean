import Mathlib
/-! # Finite probability tools used in the compression and the dyadic model -/

open Function Set Filter
open scoped BigOperators
noncomputable section

namespace OAI

namespace FourierLLogL
universe u v w w'

private def lawSet (α : Type u) [Fintype α] : Set (α → ℝ) :=
  {f | (∀ x, 0 ≤ f x) ∧ ∑ x, f x = 1}

abbrev Law (α : Type u) [Fintype α] : Type u := lawSet α

instance {α : Type u} [Fintype α] : FunLike (Law α) α ℝ where
  coe P := P.val
  coe_injective := by aesop

instance {α : Type u} [Fintype α] : CompactSpace (Law α) := by
  apply isCompact_iff_compactSpace.mp
  have hclosed : IsClosed (lawSet α) := by
    have heq : lawSet α =
        (⋂ x, {f : α → ℝ | 0 ≤ f x}) ∩ {f | ∑ x, f x = 1} := by
      ext f
      simp [lawSet]
    rw [heq]
    exact (isClosed_iInter (fun x =>
      isClosed_le continuous_const (continuous_apply x))).inter
      (isClosed_eq (by fun_prop) continuous_const)
  apply IsCompact.of_isClosed_subset
    (isCompact_Icc : IsCompact (Set.Icc (0 : α → ℝ) 1)) hclosed
  intro f hf
  rcases hf with ⟨h0, hsum⟩
  constructor
  · exact fun x => h0 x
  · intro x
    change f x ≤ (1 : ℝ)
    rw [← hsum]
    exact Finset.single_le_sum (fun y _ => h0 y) (Finset.mem_univ x)

namespace Law
variable {α : Type u} {β : Type v} {γ : Type w} {η : Type w'}
  [Fintype α] [Fintype β] [Fintype γ] [Fintype η]

protected lemma ext {P Q : Law α} (h : ∀ x, P x = Q x) : P = Q :=
  DFunLike.ext _ _ h

protected lemma nonneg (P : Law α) (x) : 0 ≤ P x := P.property.1 x

protected lemma total (P : Law α) : ∑ x, P x = 1 := P.property.2

lemma mem_nonempty (P : Law α) : ∃ x, 0 < P x := by
  by_contra! hh
  have hi : ∑ x, P x ≤ 0 := Finset.sum_nonpos fun x _ => hh x
  rw [P.total] at hi; norm_num at hi

def Ex (P : Law α) (f : α → ℝ) : ℝ := ∑ x, P x * f x

lemma Ex_const (P : Law α) (c : ℝ) : P.Ex (fun _ => c) = c := by
  rw [Ex, ← Finset.sum_mul, P.total, one_mul]

lemma Ex_add (P : Law α) (f g : α → ℝ) :
    P.Ex (fun x => f x + g x) = P.Ex f + P.Ex g := by
  simp_rw [Ex, mul_add, Finset.sum_add_distrib]

lemma Ex_sub (P : Law α) (f g : α → ℝ) :
    P.Ex (fun x => f x - g x) = P.Ex f - P.Ex g := by
  simp_rw [Ex, mul_sub, Finset.sum_sub_distrib]

lemma Ex_mul (P : Law α) (f : α → ℝ) (c : ℝ) :
    P.Ex (fun x => f x * c) = P.Ex f * c := by
  simp_rw [Ex, ← mul_assoc, Finset.sum_mul]

lemma Ex_lmul (P : Law α) (f : α → ℝ) (c : ℝ) :
    P.Ex (fun x => c * f x) = c * P.Ex f := by
  simpa only [mul_comm c] using Ex_mul P f c

lemma Ex_neg (P : Law α) (f : α → ℝ) :
    P.Ex (fun x => -f x) = -P.Ex f := by
  simpa only [neg_one_mul] using Ex_lmul P f (-1)

lemma Ex_finset_sum {ι : Type*} (s : Finset ι) (P : Law α) (f : ι → α → ℝ) :
    P.Ex (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, P.Ex (f i) := by
  unfold Ex
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

lemma Ex_mono_mem (P : Law α) {f g : α → ℝ}
    (h : ∀ x, 0 < P x → f x ≤ g x) : P.Ex f ≤ P.Ex g := by
  refine Finset.sum_le_sum fun x _ => ?_
  obtain hP | hP := eq_or_lt_of_le (P.nonneg x)
  · rw [← hP, zero_mul, zero_mul]
  · exact mul_le_mul_of_nonneg_left (h x hP) hP.le

lemma Ex_mono (P : Law α) {f g : α → ℝ}
    (h : ∀ x, f x ≤ g x) : P.Ex f ≤ P.Ex g := P.Ex_mono_mem fun x _ => h x

lemma Ex_nonneg (P : Law α) {f : α → ℝ} (h : ∀ x, 0 ≤ f x) : 0 ≤ P.Ex f := by
  simpa only [Ex_const] using P.Ex_mono h

lemma Ex_congr_mem (P : Law α) {f g : α → ℝ}
    (h : ∀ x, 0 < P x → f x = g x) : P.Ex f = P.Ex g :=
  le_antisymm (P.Ex_mono_mem fun x hx => (h x hx).le)
    (P.Ex_mono_mem fun x hx => (h x hx).ge)

lemma exists_le_Ex (P : Law α) (f : α → ℝ) : ∃ x, 0 < P x ∧ f x ≤ P.Ex f := by
  by_contra! hh
  obtain ⟨a,ha⟩ := P.mem_nonempty
  have H : P.Ex (fun _ => P.Ex f) < P.Ex f := by
    refine Finset.sum_lt_sum (fun x _ => ?_) ⟨a,Finset.mem_univ _,?_⟩
    · obtain hP | hP := eq_or_lt_of_le (P.nonneg x)
      · rw [← hP,zero_mul,zero_mul]
      · exact mul_le_mul_of_nonneg_left (hh x hP).le hP.le
    · exact mul_lt_mul_of_pos_left (hh a ha) ha
  rw [Ex_const] at H
  exact (lt_irrefl _ H)

lemma exists_Ex_le (P : Law α) (f : α → ℝ) : ∃ x, 0 < P x ∧ P.Ex f ≤ f x := by
  obtain ⟨x,hx,h⟩ := P.exists_le_Ex fun x => -f x
  exact ⟨x,hx, by simpa only [Ex_neg, neg_le_neg_iff] using h⟩

open scoped Classical
def prob (P : Law α) (p : α → Prop) : ℝ := P.Ex (fun x => if p x then 1 else 0)

lemma prob_eq (P : Law α) (p : α → Prop) [DecidablePred p] :
    P.prob p = ∑ x, if p x then P x else 0 := by simp only [prob, Ex, mul_ite, mul_one, mul_zero]

lemma prob_nonneg (P : Law α) (p : α → Prop) : 0 ≤ P.prob p :=
  Ex_nonneg P (fun x => by split_ifs <;> norm_num)

lemma prob_le_one (P : Law α) (p : α → Prop) : P.prob p ≤ 1 := by
  refine le_trans (b:=P.Ex fun _ => 1) (Ex_mono P fun x => ?_) (P.Ex_const 1).le
  split_ifs <;> norm_num

lemma mem_le_prob (P : Law α) {p : α → Prop} {x} (h : p x) : P x ≤ P.prob p := by
  rw [prob_eq]
  let f (x : α) := if p x then P x else 0
  have h' (x) : 0 ≤ f x := by unfold f; split_ifs with H; exact P.nonneg _; exact le_rfl
  change P x ≤ ∑ y, f y
  rw [show P x = f x from (ite_eq_left h).symm]
  exact Finset.single_le_sum (fun x _ => h' x) (Finset.mem_univ _)

lemma prob_pos_iff (P : Law α) (p : α → Prop) :
    0 < P.prob p ↔ ∃ x, p x ∧ 0 < P x := by
  constructor
  · intro ha
    by_contra! h
    rw [prob_eq] at ha
    refine (not_lt_of_ge (Finset.sum_nonpos fun x _ => ?_) ha)
    split_ifs with hh; exact h _ hh; exact le_rfl
  · rintro ⟨x,hx,h⟩; exact lt_of_lt_of_le h (mem_le_prob P hx)

lemma prob_single (P : Law α) (x : α) : P.prob (· = x) = P x := by simp [prob_eq]

lemma prob_compl (P : Law α) (p : α → Prop) : P.prob (fun x => ¬ p x) = 1 - P.prob p := by
  unfold prob
  calc
    _ = P.Ex (fun x => 1-(if p x then 1 else 0)) := by congr 1; funext x; split_ifs <;> simp_all
    _ = _ := by rw [Ex_sub (f:=fun _ => 1), Ex_const]

lemma ext_of_Ex {P Q : Law α} (h : ∀ f : α → ℝ, P.Ex f = Q.Ex f) : P = Q := by
  apply Law.ext; intro x
  have H := h (fun a => if a=x then 1 else 0)
  change P.prob (· = x) = Q.prob (· = x) at H
  simpa only [prob_single] using H

def point (x : α) : Law α := by
  classical
  exact ⟨Pi.single x 1, (fun y => by by_cases h : y = x <;> simp [h]), by simp⟩

lemma point_apply (x y : α) [DecidableEq α] :
    point x y = (if y=x then 1 else 0) := by
  classical
  change (point x).val y = _
  by_cases h : y = x <;> simp [point, h]

@[simp] lemma Ex_point (x : α) (f : α → ℝ) : (point x).Ex f = f x := by
  simp [Ex, point_apply]

def uniform (α : Type u) [Fintype α] [Nonempty α] : Law α :=
  ⟨fun _ => (Fintype.card α : ℝ)⁻¹, fun _ => by positivity, by simp [Fintype.card_ne_zero]⟩

lemma uniform_apply [Nonempty α] (x : α) : uniform α x = (Fintype.card α : ℝ)⁻¹ := rfl

/-- First draw from P, then apply a channel. -/
def through (P : Law α) (k : α → Law β) : Law β :=
  ⟨fun y => P.Ex (fun x => k x y), fun _ => Ex_nonneg _ (fun x => (k x).nonneg _), by
    simp_rw [← Ex_finset_sum _ P (fun y x => k x y), Law.total, Ex_const]⟩


lemma through_apply (P : Law α) (k : α → Law β) (y) : P.through k y = P.Ex (fun x => k x y) := rfl

lemma Ex_through (P : Law α) (k : α → Law β) (f : β → ℝ) :
    (P.through k).Ex f = P.Ex (fun x => (k x).Ex f) := by
  rw [Ex]
  simp_rw [through_apply, ← Ex_mul, ← Ex_finset_sum]
  rfl

/-- First draw from P, then apply a channel, retaining the original. -/
def withNext (P : Law α) (k : α → Law β) : Law (α × β) :=
  ⟨fun z => P z.1 * k z.1 z.2, fun z => mul_nonneg (P.nonneg _) ((k z.1).nonneg _), by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, Law.total, mul_one]⟩

lemma withNext_apply (P : Law α) (k : α → Law β) (a : α) (b : β) :
    P.withNext k (a,b) = P a * k a b := rfl

lemma Ex_withNext (P : Law α) (k : α → Law β) (f : α × β → ℝ) :
    (P.withNext k).Ex f = P.Ex (fun x => (k x).Ex (fun y => f (x,y))) := by
  rw [Ex,Fintype.sum_prod_type]
  simp only [Ex, withNext_apply, mul_assoc, Finset.mul_sum]

def tensorP (P : Law α) (Q : Law β) := withNext P (fun _ => Q)

lemma tensorP_apply (P : Law α) (Q : Law β) (a : α) (b : β) :
    P.tensorP Q (a,b) = P a * Q b := rfl

lemma Ex_tensorP (P : Law α) (Q : Law β) (f : α × β → ℝ) :
    (P.tensorP Q).Ex f = P.Ex fun x => Q.Ex fun y => f (x,y) :=
  Ex_withNext _ _ _

/-- Law of a function (random variable). -/
def send (P : Law α) (X : α → β) : Law β := P.through (fun x => point (X x))

lemma send_apply (P : Law α) (X : α → β) (y) : P.send X y = P.prob (fun x => X x = y) := by
  simp_rw [send, through_apply, point_apply, prob, eq_comm]

lemma Ex_send (P : Law α) (X : α → β) (f : β → ℝ) :
    (P.send X).Ex f = P.Ex fun x => f (X x) := by simp_rw [send, Ex_through, Ex_point]

lemma send_send (P : Law α) (X : α → β) (Y : β → γ) :
    (P.send X).send Y = P.send (fun x => Y (X x)) := by
  apply ext_of_Ex; intro f; simp_rw [Ex_send]

@[simp] lemma send_id (P : Law α) : P.send (fun x => x) = P := by
  apply ext_of_Ex; intro f; exact Ex_send _ _ _

lemma le_send (P : Law α) (X : α → β) (x) : P x ≤ P.send X (X x) := by
  rw [send_apply]; exact mem_le_prob P (p:=fun y => X y = X x) rfl

lemma send_pos (P : Law α) (X : α → β) {x} (h : 0 < P x) :
    0 < P.send X (X x) := lt_of_lt_of_le h (le_send P X x)

lemma send_pos_iff (P : Law α) (X : α → β) (y) :
    0 < P.send X y ↔ ∃ x, X x = y ∧ 0 < P x := by rw [send_apply]; apply prob_pos_iff

lemma send_congr_mem (P : Law α) {X Y : α → β} (h : ∀ x, 0 < P x → X x = Y x) :
    P.send X = P.send Y := by
  apply ext_of_Ex; intro f
  rw [Ex_send,Ex_send]
  exact Ex_congr_mem _ fun x hx => congrArg f (h x hx)

lemma send_fst_withNext (P : Law α) (k : α → Law β) :
    (P.withNext k).send Prod.fst = P := by
  apply ext_of_Ex; intro f
  simp_rw [Ex_send,Ex_withNext,Ex_const]

lemma send_snd_withNext (P : Law α) (k : α → Law β) :
    (P.withNext k).send Prod.snd = P.through k := by
  apply ext_of_Ex; intro f
  simp_rw [Ex_send,Ex_withNext,Ex_through]

lemma send_tensorP (P : Law α) (Q : Law β) (X : α → γ) (Y : β → η) :
    (P.tensorP Q).send (fun p => (X p.1, Y p.2)) = (P.send X).tensorP (Q.send Y) := by
  apply ext_of_Ex; intro f
  simp_rw [Ex_tensorP, Ex_send, Ex_tensorP]

lemma send_fst_tensorP (P : Law α) (Q : Law β) :
    (P.tensorP Q).send Prod.fst = P := send_fst_withNext _ _

lemma send_snd_tensorP (P : Law α) (Q : Law β) :
    (P.tensorP Q).send Prod.snd = Q := by
  apply ext_of_Ex; intro f
  simp_rw [Ex_send,Ex_tensorP,Ex_const]


/-- Conditional distribution on an event; returns the old law when probability is zero. -/
def condP (P : Law α) (p : α → Prop) : Law α :=
  if hp : 0 < P.prob p then
    ⟨fun x => (if p x then P x else 0) / P.prob p,
      fun x => div_nonneg (by split_ifs; exact P.nonneg _; exact le_rfl) hp.le, by
      rw [← Finset.sum_div, ← prob_eq P p, div_self hp.ne']⟩
  else P

lemma condP_pos_apply (P : Law α) (p : α → Prop) [DecidablePred p]
    (hp : 0 < P.prob p) (x : α) :
    P.condP p x = (if p x then P x else 0) / P.prob p := by
  unfold condP
  rw [dite_eq_left hp]
  change @ite ℝ (p x) (Classical.propDecidable (p x)) (P x) 0 / P.prob p = _
  by_cases H : p x <;> simp [H]

lemma prob_mul_condP (P : Law α) (p : α → Prop) [DecidablePred p] (x : α) :
    P.prob p * P.condP p x = if p x then P x else 0 := by
  obtain H|H := eq_or_lt_of_le (P.prob_nonneg p)
  · rw [← H, zero_mul]
    split_ifs with h
    · exact (P.nonneg _).antisymm ((mem_le_prob P h).trans H.ge)
    · rfl
  · rw [condP_pos_apply P p H]
    field_simp

lemma condP_mem {P : Law α} {p : α → Prop} (hp : 0 < P.prob p) {x : α} :
    0 < P.condP p x ↔ p x ∧ 0 < P x := by
  rw [condP_pos_apply P _ hp, lt_div_iff₀ hp, zero_mul]
  split_ifs <;> simp_all

lemma prob_mul_Ex_condP (P : Law α) (p : α → Prop) [DecidablePred p] (f : α → ℝ) :
    P.prob p * (P.condP p).Ex f = P.Ex fun x => if p x then f x else 0 := by
  unfold Ex
  rw [Finset.mul_sum]
  simp only [← mul_assoc, prob_mul_condP, ite_mul, mul_ite, mul_zero, zero_mul]

/-- Post law after observing W=b. -/
def after (P : Law α) (W : α → β) (b : β) := P.condP (fun x => W x = b)

lemma send_mul_after (P : Law α) (W : α → β) [DecidableEq β] (b : β) (x : α) :
    P.send W b * P.after W b x = if W x = b then P x else 0 := by
  rw [send_apply]
  exact prob_mul_condP _ _ _

lemma after_mem {P : Law α} {W : α → β} {b : β} (h : 0 < P.send W b) {x : α} :
    0 < P.after W b x ↔ W x = b ∧ 0 < P x :=
  condP_mem (by rwa [send_apply] at h)

lemma after_self_pos (P : Law α) (W : α → β) {x : α} (hx : 0 < P x) :
    0 < P.after W (W x) x := (after_mem (P.send_pos W hx)).mpr ⟨rfl,hx⟩

lemma after_Ex_sum (P : Law α) (W : α → β) (f : β → α → ℝ) :
    (P.send W).Ex (fun w => (P.after W w).Ex (f w)) =
      P.Ex fun x => f (W x) x := by
  unfold Ex
  simp_rw [Finset.mul_sum, ← mul_assoc, send_mul_after]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp [ite_mul]

lemma through_after (P : Law α) (W : α → β) :
    (P.send W).through (P.after W) = P := by
  apply ext_of_Ex
  intro f
  rw [Ex_through]
  exact P.after_Ex_sum W (fun _ => f)

lemma joint_after (P : Law α) (X : α → β) (W : α → γ) (x w) :
    P.send (fun a => (X a, W a)) (x,w) = P.send W w * ((P.after W w).send X x) := by
  rw [send_apply P, send_apply (after _ _ _)]
  simp_rw [prob_eq, Finset.mul_sum, mul_ite, mul_zero, send_mul_after]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Prod.mk.injEq]
  split_ifs <;> simp_all

/-- All expectations agree iff the law agrees, so matching after a get operation can
be checked by its marginals. -/
lemma after_send_eq_of_send_pair_eq {P : Law α} {Q : Law η}
    {X : α → β} {W : α → γ} {Y : η → β} {V : η → γ}
    (h : P.send (fun a => (X a, W a)) = Q.send (fun a => (Y a, V a)))
    (w : γ) :
    (P.after W w).send X = (Q.after V w).send Y := by
  have H1 := congrArg (fun p : Law (β × γ) => p.send Prod.fst) h
  have H2 := congrArg (fun p : Law (β × γ) => p.send Prod.snd) h
  simp only [send_send] at H1 H2
  by_cases hh : 0 < P.send W w
  · apply Law.ext; intro x
    have he : P.send W w * (P.after W w).send X x =
        Q.send V w * (Q.after V w).send Y x := by rw [← joint_after, ← joint_after, h]
    rw [← H2] at he
    exact mul_left_cancel₀ hh.ne' he
  · have hh' : ¬ 0 < Q.send V w := by rwa [← H2]
    rw [send_apply] at hh hh'
    simp only [after, condP, dite_eq_right hh, dite_eq_right hh', H1]

/-- Binary mixture; real probability t for the first option. -/
def mixture (P Q : Law α) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) : Law α :=
  ⟨fun a => t * P a + (1-t) * Q a, fun a => add_nonneg
    (mul_nonneg h0 (P.nonneg a)) (mul_nonneg (by linarith) (Q.nonneg a)), by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Law.total]; ring⟩

lemma mixture_apply (P Q : Law α) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) (x : α) :
    mixture P Q t h0 h1 x = t * P x + (1-t)*Q x := rfl

lemma mixture_Ex (P Q : Law α) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) (f : α → ℝ) :
    (mixture P Q t h0 h1).Ex f = t * P.Ex f + (1-t) * Q.Ex f := by
  simp_rw [Ex,mixture_apply, add_mul,mul_assoc,Finset.sum_add_distrib,Finset.mul_sum]

lemma le_one (P : Law α) (x : α) : P x ≤ 1 := by
  calc
    P x ≤ ∑ y, P y := Finset.single_le_sum (fun y _ => P.nonneg y) (Finset.mem_univ x)
    _ = 1 := P.total

/-- Change density proportionally to a nonnegative function. -/
def proportional (w : α → ℝ) (hw : ∀ x, 0 ≤ w x) (ht : 0 < ∑ x, w x) : Law α :=
  ⟨fun x => w x / ∑ y, w y, fun x => div_nonneg (hw x) ht.le, by rw [← Finset.sum_div, div_self ht.ne']⟩

lemma proportional_apply (w : α → ℝ) (hw : ∀ x, 0 ≤ w x) (ht : 0 < ∑ x, w x) (x) :
    proportional w hw ht x = w x / ∑ y, w y := rfl

end Law
end FourierLLogL

end OAI
