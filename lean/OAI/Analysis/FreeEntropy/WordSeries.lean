import OAI.Analysis.FreeEntropy.GUELimit

namespace OAI

universe u1 u2

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α : Type u1}
abbrev Series (α : Type u2) := List α → ℂ

def unit : Series α
  | [] => 1
  | _::_ => 0

def deriv (a : α) (f : Series α) : Series α := fun w => f (a::w)

def conv (f g : Series α) : Series α
  | [] => f [] * g []
  | a::w => f [] * g (a::w) + conv (deriv a f) g w

@[simp] theorem unit_nil : (unit : Series α) [] = 1 := rfl
@[simp] theorem unit_cons (a : α) (w : List α) : unit (a::w) = 0 := rfl
@[simp] theorem conv_nil (f g : Series α) : conv f g [] = f [] * g [] := rfl
@[simp] theorem conv_cons (f g : Series α) (a : α) (w : List α) :
    conv f g (a::w) = f [] * g (a::w) + conv (deriv a f) g w := rfl
@[simp] theorem deriv_apply (a : α) (f : Series α) (w : List α) : deriv a f w = f (a::w) := rfl

 theorem conv_sum_splits (f g : Series α) (w : List α) :
    conv f g w = ∑ k ∈ range (w.length+1), f (w.take k) * g (w.drop k) := by
  induction w generalizing f with
  | nil => simp
  | cons a w ih =>
    rw [conv_cons, ih, List.length_cons]
    conv_rhs => rw [sum_range_succ']
    simp only [List.take_zero, List.drop_zero, List.take_succ_cons, List.drop_succ_cons, deriv_apply]
    ring

 theorem conv_add_left (f g h : Series α) : conv (f+g) h = conv f h + conv g h := by
  funext w
  simp only [conv_sum_splits, Pi.add_apply, add_mul, sum_add_distrib]
 theorem conv_add_right (f g h : Series α) : conv f (g+h) = conv f g + conv f h := by
  funext w
  simp only [conv_sum_splits, Pi.add_apply, mul_add, sum_add_distrib]
 theorem conv_smul_left (c : ℂ) (f g : Series α) : conv (c • f) g = c • conv f g := by
  funext w
  simp only [conv_sum_splits, Pi.smul_apply, smul_eq_mul, mul_assoc, mul_sum]
 theorem conv_smul_right (c : ℂ) (f g : Series α) : conv f (c • g) = c • conv f g := by
  funext w
  simp only [conv_sum_splits, Pi.smul_apply, smul_eq_mul, mul_sum]
  apply sum_congr rfl
  intro k _
  ring
@[simp] theorem conv_zero_left (f : Series α) : conv 0 f = 0 := by
  funext w
  simp [conv_sum_splits]
@[simp] theorem conv_zero_right (f : Series α) : conv f 0 = 0 := by
  funext w
  simp [conv_sum_splits]
 theorem deriv_conv (a : α) (f g : Series α) :
    deriv a (conv f g) = f [] • deriv a g + conv (deriv a f) g := rfl
@[simp] theorem deriv_unit (a : α) : deriv a (unit : Series α) = 0 := rfl

@[simp] theorem conv_unit_left (f : Series α) : conv unit f = f := by
  funext w
  cases w <;> simp [conv, deriv_unit]
@[simp] theorem conv_unit_right (f : Series α) : conv f unit = f := by
  funext w
  induction w generalizing f with
  | nil => simp
  | cons a w ih => simp [ih]

 theorem conv_assoc (f g h : Series α) : conv (conv f g) h = conv f (conv g h) := by
  funext w
  induction w generalizing f g h with
  | nil => simp [mul_assoc]
  | cons a w ih =>
    simp only [conv_cons, conv_nil, deriv_conv, conv_add_left, conv_smul_left,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, ih]
    ring

 theorem conv_neg_left (f g : Series α) : conv (-f) g = -conv f g := by
  simpa using conv_smul_left (-1) f g
 theorem conv_neg_right (f g : Series α) : conv f (-g) = -conv f g := by
  simpa using conv_smul_right (-1) f g
 theorem conv_sub_left (f g h : Series α) : conv (f-g) h = conv f h - conv g h := by
  simp [sub_eq_add_neg, conv_add_left, conv_neg_left]
 theorem conv_sub_right (f g h : Series α) : conv f (g-h) = conv f g - conv f h := by
  simp [sub_eq_add_neg, conv_add_right, conv_neg_right]

 def Agree (n : ℕ) (f g : Series α) : Prop := ∀ w, w.length ≤ n → f w = g w
 theorem conv_agree {n : ℕ} {f f' g g' : Series α} (hf : Agree n f f') (hg : Agree n g g') :
    Agree n (conv f g) (conv f' g') := by
  intro w hw
  simp only [conv_sum_splits]
  apply sum_congr rfl
  intro k hk
  rw [hf _ (by simp only [List.length_take]; omega),
    hg _ (by simp only [List.length_drop]; omega)]

theorem length_induction {P : List α → Prop} (w : List α)
    (h : ∀ w, (∀ v, v.length < w.length → P v) → P w) : P w :=
  (measure List.length).wf.induction w h

def subst (M f : Series α) : Series α
  | [] => f []
  | a::w => ∑ k ∈ range (w.length+1), M (w.take k) * subst M (deriv a f) (w.drop k)
termination_by w => w.length

@[simp] theorem subst_nil (M f : Series α) : subst M f [] = f [] := by rw [subst]
 theorem subst_cons (M f : Series α) (a : α) (w : List α) :
    subst M f (a::w) = conv M (subst M (deriv a f)) w := by
  rw [subst, conv_sum_splits]
 theorem deriv_subst (M f : Series α) (a : α) :
    deriv a (subst M f) = conv M (subst M (deriv a f)) := by
  funext w
  exact subst_cons M f a w

 theorem subst_add (M f g : Series α) : subst M (f+g) = subst M f + subst M g := by
  funext w
  induction w using length_induction generalizing f g with
  | h w ih =>
    cases w with
    | nil => simp
    | cons a w =>
      simp only [subst, Pi.add_apply]
      simp_rw [show deriv a (f+g) = deriv a f + deriv a g from rfl]
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro k hk
      rw [ih _ (by simp)]
      simp [mul_add]

 theorem subst_smul (M f : Series α) (c : ℂ) : subst M (c • f) = c • subst M f := by
  funext w
  induction w using length_induction generalizing f with
  | h w ih =>
    cases w with
    | nil => simp
    | cons a w =>
      simp only [subst, Pi.smul_apply, smul_eq_mul]
      simp_rw [show deriv a (c • f) = c • deriv a f from rfl]
      rw [mul_sum]
      apply sum_congr rfl
      intro k hk
      rw [ih _ (by simp)]
      simp [mul_left_comm]

@[simp] theorem subst_zero (M : Series α) : subst M 0 = 0 := by
  have h := subst_smul M 0 0
  simpa using h
@[simp] theorem subst_unit (M : Series α) : subst M unit = unit := by
  funext w
  cases w with
  | nil => simp
  | cons a w => simp [subst_cons]

 theorem subst_mul (M f g : Series α) : subst M (conv f g) = conv (subst M f) (subst M g) := by
  funext w
  induction w using length_induction generalizing f g with
  | h w ih =>
    cases w with
    | nil => simp
    | cons a w =>
      rw [subst_cons, deriv_conv, subst_add, subst_smul, conv_add_right, conv_smul_right]
      rw [conv_cons, subst_nil, subst_cons, deriv_subst, conv_assoc]
      change f [] * _ + _ = f [] * _ + _
      congr 1
      apply conv_agree (n := w.length) (fun _ _ => rfl) (fun v hv => ?_) w le_rfl
      exact ih v (by simp ; omega) _ _

 theorem subst_neg (M f : Series α) : subst M (-f) = -subst M f := by
  simpa using subst_smul M f (-1)
 theorem subst_sub (M f g : Series α) : subst M (f-g) = subst M f - subst M g := by
  simp [sub_eq_add_neg, subst_add, subst_neg]

 theorem subst_unit_left (f : Series α) : subst unit f = f := by
  funext w
  induction w generalizing f with
  | nil => simp
  | cons a w ih => rw [subst_cons, conv_unit_left, ih]; rfl

theorem subst_comp (L M f : Series α) :
    subst L (subst M f) = subst (conv L (subst L M)) f := by
  funext w
  induction w using length_induction generalizing f with
  | h w ih =>
    cases w with
    | nil => simp
    | cons a w =>
      rw [subst_cons, deriv_subst, subst_mul, ← conv_assoc, subst_cons]
      apply conv_agree (n := w.length) (fun _ _ => rfl) (fun v hv => ?_) w le_rfl
      exact ih v (by simp ; omega) _

end FiniteEntropySeparation.FreeSeries

end

end OAI
