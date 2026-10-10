import OAI.Analysis.FreeEntropy.SemicircularSeries

namespace OAI

universe u1 u2 u3 u4

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α : Type} [DecidableEq α] [Fintype α]

def rightDeriv (i : α) (f : Series α) : Series α := fun w => f (w ++ [i])
def Cyclic (f : Series α) : Prop := ∀ i, deriv i f = rightDeriv i f
@[simp] theorem rightDeriv_apply {α : Type} [DecidableEq α] [Fintype α] (i : α) (f : Series α) (w : List α) :
    rightDeriv i f w = f (w ++ [i]) := rfl
 theorem rightDeriv_conv {α : Type} [DecidableEq α] [Fintype α] (i : α) (f g : Series α) :
    rightDeriv i (conv f g) = conv f (rightDeriv i g) + g [] • rightDeriv i f := by
  funext w
  induction w generalizing f with
  | nil => simp [rightDeriv, deriv, conv]; ring
  | cons a w ih =>
    change f [] * g ((a::w)++[i]) + conv (deriv a f) g (w++[i]) =
      (f [] * g ((a::w)++[i]) + conv (deriv a f) (rightDeriv i g) w) +
      g [] * f ((a::w)++[i])
    have h := ih (deriv a f)
    change conv (deriv a f) g (w++[i]) = _ at h
    rw [h]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, rightDeriv_apply, deriv_apply, List.cons_append]
    ring
 theorem rightDeriv_conv' (i : α) (f g : Series α) :
    rightDeriv i (conv f g) = conv f (rightDeriv i g) + g [] • rightDeriv i f :=
  rightDeriv_conv i f g
@[simp] theorem rightDeriv_unit {α : Type} [DecidableEq α] [Fintype α] (i : α) : rightDeriv i (unit : Series α) = 0 := by
  funext w
  cases w <;> rfl
@[simp] theorem rightDeriv_zero {α : Type} [DecidableEq α] [Fintype α] (i : α) : rightDeriv i (0 : Series α) = 0 := rfl
 theorem rightDeriv_add {α : Type} [DecidableEq α] [Fintype α] (i : α) (f g : Series α) :
    rightDeriv i (f+g) = rightDeriv i f + rightDeriv i g := rfl
 theorem rightDeriv_sub {α : Type} [DecidableEq α] [Fintype α] (i : α) (f g : Series α) :
    rightDeriv i (f-g) = rightDeriv i f - rightDeriv i g := rfl
 theorem rightDeriv_smul {α : Type} [DecidableEq α] [Fintype α] (i : α) (c : ℂ) (f : Series α) :
    rightDeriv i (c • f) = c • rightDeriv i f := rfl
 theorem rightDeriv_sum {α : Type} [DecidableEq α] [Fintype α] {β : Type u1} (s : Finset β) (f : β → Series α) (i : α) :
    rightDeriv i (∑ b ∈ s, f b) = ∑ b ∈ s, rightDeriv i (f b) := by
  funext w
  simp [rightDeriv]
 theorem rightDeriv_letter {α : Type} [DecidableEq α] [Fintype α] (i j : α) : rightDeriv i (letter j) = if i=j then unit else 0 := by
  funext w
  cases w with
  | nil => by_cases h : i=j <;> simp [rightDeriv, letter, unit, h]
  | cons a w => cases w <;> by_cases h : i=j <;> simp [rightDeriv, letter, unit, h]
 theorem series_ext_right {α : Type} [DecidableEq α] [Fintype α] {f g : Series α} (hn : f [] = g [])
    (h : ∀ i, rightDeriv i f = rightDeriv i g) : f = g := by
  funext w
  induction w using List.reverseRecOn with
  | nil => exact hn
  | append_singleton w i _ => exact congrFun (h i) w

def rightAssemble (f : α → Series α) : Series α := ∑ i, conv (f i) (letter i)
@[simp] theorem rightAssemble_nil (f : α → Series α) : rightAssemble f [] = 0 := by
  simp [rightAssemble]
 theorem rightDeriv_assemble (f : α → Series α) (j : α) :
    rightDeriv j (rightAssemble f) = f j := by
  rw [rightAssemble, rightDeriv_sum]
  simp only [rightDeriv_conv, rightDeriv_letter, letter_nil, zero_smul, add_zero]
  have hh (i : α) : conv (f i) (if j=i then unit else 0) = if j=i then f i else 0 := by
    split_ifs <;> simp
  simp_rw [hh]
  simp
 theorem assemble_rightDeriv (f : Series α) :
    rightAssemble (fun i => rightDeriv i f) = f - f [] • unit := by
  apply series_ext_right
  · simp
  · intro i
    simp [rightDeriv_assemble, rightDeriv_sub, rightDeriv_smul]
 theorem Cyclic.assemble {f : Series α} (hf : Cyclic f) :
    rightAssemble (fun i => deriv i f) = f - f [] • unit := by
  have hh : (fun i => deriv i f) = (fun i => rightDeriv i f) := funext hf
  rw [hh, assemble_rightDeriv]
 theorem cyclic_of_assemble {f : Series α} (h : rightAssemble (fun i => deriv i f) = f - f [] • unit) :
    Cyclic f := by
  intro i
  have hh := congrArg (rightDeriv i) h
  simpa [rightDeriv_assemble, rightDeriv_sub, rightDeriv_smul] using hh

 theorem conv_sum_left {α : Type} [DecidableEq α] [Fintype α] {β : Type u2} (s : Finset β) (f : β → Series α) (g : Series α) :
    conv (∑ b ∈ s, f b) g = ∑ b ∈ s, conv (f b) g := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert b s hb ih => simp [sum_insert hb, conv_add_left, ih]
 theorem conv_sum_right {α : Type} [DecidableEq α] [Fintype α] {β : Type u3} (s : Finset β) (f : Series α) (g : β → Series α) :
    conv f (∑ b ∈ s, g b) = ∑ b ∈ s, conv f (g b) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert b s hb ih => simp [sum_insert hb, conv_add_right, ih]
 theorem subst_sum {α : Type} [DecidableEq α] [Fintype α] {β : Type u4} (s : Finset β) (M : Series α) (f : β → Series α) :
    subst M (∑ b ∈ s, f b) = ∑ b ∈ s, subst M (f b) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert b s hb ih => simp [sum_insert hb, subst_add, ih]
 theorem subst_letter {α : Type} [DecidableEq α] [Fintype α] (M : Series α) (i : α) : subst M (letter i) = conv (letter i) M := by
  funext w
  cases w with
  | nil => simp
  | cons j w => simp only [subst_letter_cons, conv_cons, letter_nil, zero_mul, zero_add,
      deriv_letter]; split_ifs <;> simp
 theorem subst_rightAssemble (M : Series α) (f : α → Series α) :
    subst M (rightAssemble f) = conv (rightAssemble (fun i => subst M (f i))) M := by
  simp only [rightAssemble, subst_sum, conv_sum_left, subst_mul, subst_letter, conv_assoc]

 theorem cyclic_cumulants {M : Series α} (hM : M [] = 1) (hc : Cyclic M) :
    Cyclic (cumulants M) := by
  let R := cumulants M
  have he : M = unit + subst M R := cumulants_equation hM
  have hd (i : α) : deriv i M = conv M (subst M (deriv i R)) := by
    funext w
    have h := congrFun he (i::w)
    simpa [subst_cons] using h
  have hi (i : α) : rightDeriv i (inverse M) = -subst M (deriv i R) := by
    have hh := congrArg (rightDeriv i) (inverse_conv hM)
    rw [rightDeriv_conv, rightDeriv_unit, hM, one_smul, ← hc i, hd i,
      ← conv_assoc, inverse_conv hM, conv_unit_left] at hh
    exact eq_neg_of_add_eq_zero_right hh
  have hinv : rightAssemble (fun i => subst M (deriv i R)) = unit - inverse M := by
    apply series_ext_right
    · simp
    · intro i
      simp [rightDeriv_assemble, rightDeriv_sub, hi]
  apply cyclic_of_assemble
  simp only [cumulants_nil, zero_smul, sub_zero]
  apply subst_injective hM
  rw [subst_rightAssemble, hinv, conv_sub_left, conv_unit_left, inverse_conv hM]
  exact (eq_sub_iff_add_eq.mpr (by simpa [add_comm] using he.symm)).symm

 theorem cyclic_moments {R : Series α} (hR : R [] = 0) (hc : Cyclic R) :
    Cyclic (moments R) := by
  let M := moments R
  have hM : M [] = 1 := moments_nil R
  have he : M = unit + subst M R := moments_eq hR
  let A := rightAssemble (fun i => subst M (deriv i R))
  have hr : subst M R = conv A M := by
    have h := hc.assemble
    rw [hR, zero_smul, sub_zero] at h
    rw [← h, subst_rightAssemble]
  have ha : unit - A = inverse M := by
    have hp : conv (unit - A) M = unit := by
      rw [conv_sub_left, conv_unit_left]
      rw [hr] at he
      exact sub_eq_iff_eq_add.mpr he
    calc
      unit - A = conv (unit - A) (conv M (inverse M)) := by rw [conv_inverse hM, conv_unit_right]
      _ = inverse M := by rw [← conv_assoc, hp, conv_unit_left]
  intro i
  have hi : rightDeriv i (inverse M) = -subst M (deriv i R) := by
    rw [← ha, rightDeriv_sub, rightDeriv_unit, sub_eq_add_neg, zero_add]
    change -rightDeriv i (rightAssemble _) = _
    rw [rightDeriv_assemble]
  have hh := congrArg (rightDeriv i) (conv_inverse hM)
  rw [rightDeriv_conv, rightDeriv_unit, inverse_nil, one_smul, hi, conv_neg_right] at hh
  have hh' : rightDeriv i M = conv M (subst M (deriv i R)) := by
    exact eq_of_sub_eq_zero (by rw [sub_eq_add_neg]; simpa [add_comm] using hh)
  rw [hh']
  funext w
  have h := congrFun he (i::w)
  simpa [subst_cons] using h

end FiniteEntropySeparation.FreeSeries

end

end OAI
