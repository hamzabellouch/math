import OAI.Analysis.FreeEntropy.WordSeries

namespace OAI

universe u1

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α : Type u1}

 theorem Agree.mono {n m : ℕ} {f g : Series α} (h : Agree n f g) (hmn : m ≤ n) :
    Agree m f g := fun w hw => h w (hw.trans hmn)
 theorem Agree.refl (n : ℕ) (f : Series α) : Agree n f f := fun _ _ => rfl
 theorem Agree.symm {n : ℕ} {f g : Series α} (h : Agree n f g) : Agree n g f :=
  fun w hw => (h w hw).symm
 theorem Agree.trans {n : ℕ} {f g h : Series α} (hfg : Agree n f g) (hgh : Agree n g h) :
    Agree n f h := fun w hw => (hfg w hw).trans (hgh w hw)
 theorem agree_add {n : ℕ} {f f' g g' : Series α} (hf : Agree n f f') (hg : Agree n g g') :
    Agree n (f+g) (f'+g') := fun w hw => by simp only [Pi.add_apply, hf w hw, hg w hw]
 theorem agree_deriv {n : ℕ} {f g : Series α} (h : Agree (n+1) f g) (a : α) :
    Agree n (deriv a f) (deriv a g) := fun w hw => h (a::w) (by simp; omega)

 theorem subst_agree {n : ℕ} {M M' f g : Series α} (hM : Agree n M M') (hf : Agree n f g) :
    Agree n (subst M f) (subst M' g) := by
  induction n generalizing M M' f g with
  | zero =>
    intro w hw
    have : w = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hw)
    subst w
    simpa using hf [] (by simp)
  | succ n ih =>
    intro w hw
    cases w with
    | nil => simpa using hf [] (by simp)
    | cons a w =>
      simp only [subst_cons]
      exact conv_agree (hM.mono (by omega))
        (ih (hM.mono (by omega)) (agree_deriv hf a)) w (by simp at hw; omega)

 theorem subst_agree_left_step {n : ℕ} {M M' : Series α} (hM : Agree n M M') (f : Series α) :
    Agree (n+1) (subst M f) (subst M' f) := by
  intro w hw
  cases w with
  | nil => simp
  | cons a w =>
    simp only [subst_cons]
    exact conv_agree hM (subst_agree hM (Agree.refl _ _)) w (by simp at hw; omega)

 theorem conv_left_cancel {M f g : Series α} (hM : M [] = 1)
    (h : conv M f = conv M g) : f = g := by
  funext w
  induction w using length_induction with
  | h w ih =>
    cases w with
    | nil => simpa [hM] using congrFun h []
    | cons a w =>
      have ht := congrFun h (a::w)
      simp only [conv_cons, hM, one_mul] at ht
      have hsmall : conv (deriv a M) f w = conv (deriv a M) g w := by
        apply conv_agree (Agree.refl w.length _) (fun v hv => ih v (by simp; omega)) w le_rfl
      rw [hsmall] at ht
      exact add_right_cancel ht

 theorem subst_injective {M : Series α} (hM : M [] = 1) : Function.Injective (subst M) := by
  intro f g h
  funext w
  induction w generalizing f g with
  | nil => simpa using congrFun h []
  | cons a w ih =>
    apply ih
    apply conv_left_cancel hM
    change conv M (subst M (deriv a f)) = conv M (subst M (deriv a g))
    rw [← deriv_subst, ← deriv_subst, h]

def inverse (f : Series α) : Series α
  | [] => 1
  | a::w => - ∑ k ∈ range (w.length+1), f (a::w.take k) * inverse f (w.drop k)
termination_by w => w.length

@[simp] theorem inverse_nil (f : Series α) : inverse f [] = 1 := by rw [inverse]
 theorem inverse_cons (f : Series α) (a : α) (w : List α) :
    inverse f (a::w) = -conv (deriv a f) (inverse f) w := by
  rw [inverse, conv_sum_splits]
  rfl
 theorem conv_inverse {f : Series α} (hf : f [] = 1) : conv f (inverse f) = unit := by
  funext w
  cases w with
  | nil => simp [hf]
  | cons a w => simp [inverse_cons, hf]
 theorem inverse_conv {f : Series α} (hf : f [] = 1) : conv (inverse f) f = unit := by
  apply conv_left_cancel hf
  rw [← conv_assoc, conv_inverse hf, conv_unit_left, conv_unit_right]
 theorem inverse_unique {f g : Series α} (hf : f [] = 1) (hg : conv f g = unit) :
    g = inverse f := conv_left_cancel hf (hg.trans (conv_inverse hf).symm)
 theorem inverse_inverse {f : Series α} (hf : f [] = 1) : inverse (inverse f) = f :=
  (inverse_unique (inverse_nil f) (inverse_conv hf)).symm
 theorem subst_inverse (M : Series α) {f : Series α} (hf : f [] = 1) :
    subst M (inverse f) = inverse (subst M f) := by
  apply inverse_unique (by simpa using hf)
  rw [← subst_mul, conv_inverse hf, subst_unit]

def momentIter (R : Series α) : ℕ → Series α
  | 0 => unit
  | n+1 => unit + subst (momentIter R n) R

@[simp] theorem momentIter_nil {R : Series α} (hR : R [] = 0) (n : ℕ) :
    momentIter R n [] = 1 := by
  cases n <;> simp [momentIter, hR]
 theorem momentIter_step {R : Series α} (hR : R [] = 0) (n : ℕ) :
    Agree n (momentIter R (n+1)) (momentIter R n) := by
  induction n with
  | zero =>
    intro w hw
    have : w = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hw)
    subst w
    simp [momentIter, hR]
  | succ n ih =>
    exact agree_add (Agree.refl _ _) (subst_agree_left_step ih R)
 theorem momentIter_stable {R : Series α} (hR : R [] = 0) {n m : ℕ} (hnm : n ≤ m) :
    Agree n (momentIter R m) (momentIter R n) := by
  induction m, hnm using Nat.le_induction with
  | base => exact Agree.refl _ _
  | succ m hnm ih => exact ((momentIter_step hR m).mono hnm).trans ih

 def moments (R : Series α) : Series α := fun w => momentIter R w.length w
 theorem moments_agree {R : Series α} (hR : R [] = 0) (n : ℕ) :
    Agree n (moments R) (momentIter R n) := by
  intro w hw
  exact ((momentIter_stable hR hw) w le_rfl).symm
@[simp] theorem moments_nil (R : Series α) : moments R [] = 1 := rfl
 theorem moments_eq {R : Series α} (hR : R [] = 0) : moments R = unit + subst (moments R) R := by
  funext w
  have h := (moments_agree hR (w.length+1)) w (by omega)
  rw [h, momentIter]
  apply congrArg (fun z : ℂ => unit w + z)
  exact ((subst_agree_left_step (moments_agree hR w.length) R) w (by omega)).symm
 theorem moments_unique {R M : Series α} (hR : R [] = 0)
    (hM : M = unit + subst M R) : M = moments R := by
  have hn (n : ℕ) : Agree n M (momentIter R n) := by
    induction n with
    | zero =>
      intro w hw
      have : w = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hw)
      subst w
      have h := congrFun hM []
      simpa [momentIter, hR] using h
    | succ n ih =>
      rw [hM]
      exact agree_add (Agree.refl _ _) (subst_agree_left_step ih R)
  funext w
  exact hn w.length w le_rfl

def boolean (M : Series α) : Series α := unit - inverse M
 def cumulants (M : Series α) : Series α := inverse (moments (-boolean M)) - unit

@[simp] theorem boolean_nil (M : Series α) : boolean M [] = 0 := by simp [boolean]
@[simp] theorem cumulants_nil (M : Series α) : cumulants M [] = 0 := by simp [cumulants]

 theorem cumulants_equation {M : Series α} (hM : M [] = 1) :
    M = unit + subst M (cumulants M) := by
  let J := moments (-boolean M)
  have hB : (-boolean M) [] = 0 := by simp
  have hJ : J = unit - subst J (boolean M) := by
    simpa only [subst_neg, sub_eq_add_neg] using moments_eq hB
  have hJM : conv J (subst J M) = unit := by
    have hJI : J = subst J (inverse M) := by
      calc
        J = unit - subst J (boolean M) := hJ
        _ = subst J (inverse M) := by rw [boolean, subst_sub, subst_unit]; abel
    calc
      conv J (subst J M) = conv (subst J (inverse M)) (subst J M) :=
        congrArg (fun A => conv A (subst J M)) hJI
      _ = unit := by rw [← subst_mul, inverse_conv hM, subst_unit]
  have hsubst : subst J (subst M (cumulants M)) = inverse J - unit := by
    rw [subst_comp, hJM, subst_unit_left]
    rfl
  apply subst_injective (moments_nil _)
  rw [subst_add, subst_unit, hsubst]
  have hMI : subst J M = inverse J := inverse_unique (moments_nil _) hJM
  rw [hMI]
  abel

 theorem cumulants_unique {M R : Series α} (hM : M [] = 1)
    (h : M = unit + subst M R) : R = cumulants M := by
  apply subst_injective hM
  have he := cumulants_equation hM
  exact add_left_cancel (h.symm.trans he)

end FiniteEntropySeparation.FreeSeries

end

end OAI
