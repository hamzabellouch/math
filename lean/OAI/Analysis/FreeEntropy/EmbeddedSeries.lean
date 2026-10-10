import OAI.Analysis.FreeEntropy.LinearSeries

namespace OAI

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α β γ : Type} [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β]

def liftSeries (e : α → β) : Series α → Series β := reparam (fun a b => if e a=b then 1 else 0)
@[simp] theorem liftSeries_nil {α β : Type} [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β] (e : α → β) (f : Series α) : liftSeries e f [] = f [] := rfl
 theorem deriv_liftSeries (e : α → β) (f : Series α) (b : β) :
    deriv b (liftSeries e f) = ∑ a, (if e a=b then (1:ℂ) else 0) • liftSeries e (deriv a f) :=
  deriv_reparam _ _ _
 theorem deriv_liftSeries_image (e : α → β) (he : Function.Injective e) (f : Series α) (a : α) :
    deriv (e a) (liftSeries e f) = liftSeries e (deriv a f) := by
  rw [deriv_liftSeries]
  simp only [he.eq_iff, ite_smul, one_smul, zero_smul]
  simp
 theorem deriv_liftSeries_out (e : α → β) (f : Series α) (b : β)
    (hb : ∀ a, e a ≠ b) : deriv b (liftSeries e f) = 0 := by
  rw [deriv_liftSeries]
  simp [hb]
 theorem liftSeries_letter (e : α → β) (a : α) : liftSeries e (letter a) = letter (e a) := by
  funext w
  cases w with
  | nil => rfl
  | cons b w =>
    rw [liftSeries, reparam_cons]
    simp only [deriv_letter, apply_ite (reparam _), reparam_unit, reparam_zero]
    simp only [ite_apply, Pi.zero_apply, mul_ite, mul_zero]
    simp only [sum_ite_eq', mem_univ, ↓reduceIte]
    cases w with
    | nil => simp [letter, eq_comm]
    | cons d w => cases w <;> simp [letter]
 theorem restrict_liftSeries (e : α → β) (he : Function.Injective e) (f : Series α) :
    restrict e (liftSeries e f) = f := by
  funext w
  induction w generalizing f with
  | nil => rfl
  | cons a w ih =>
    change deriv (e a) (liftSeries e f) (w.map e) = f (a::w)
    rw [deriv_liftSeries_image e he]
    exact ih (deriv a f)
 theorem restrict_liftSeries_disjoint (e : α → β) (d : γ → β)
    (hd : ∀ i j, e i ≠ d j) (f : Series α) (hf : f [] = 0) :
    (fun w : List γ => liftSeries e f (w.map d)) = 0 := by
  funext w
  cases w with
  | nil => exact hf
  | cons a w =>
    change deriv (d a) (liftSeries e f) (w.map d) = 0
    rw [deriv_liftSeries_out e f (d a) (fun i => hd i a)]
    rfl

variable [DecidableEq γ] [Fintype γ]
 theorem reparam_liftSeries (e : α → β) (c : β → γ → ℂ) (f : Series α) :
    reparam c (liftSeries e f) = reparam (fun a d => c (e a) d) f := by
  funext w
  induction w generalizing f with
  | nil => rfl
  | cons d w ih =>
    rw [reparam_cons, reparam_cons]
    simp only [deriv_liftSeries, reparam_sum, reparam_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    simp_rw [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro a _
    simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_zero]
    simp only [sum_ite_eq, mem_univ, ↓reduceIte]
    rw [ih]
 theorem reparam_identity (f : Series α) : reparam (fun a b : α => if a=b then 1 else 0) f = f := by
  funext w
  have h := congrFun (restrict_liftSeries (id : α → α) Function.injective_id f) w
  change reparam (fun a b : α => if a=b then 1 else 0) f (w.map id) = f w at h
  simpa only [List.map_id] using h
 theorem reparam_scalar (z : ℂ) (f : Series α) (w : List α) :
    reparam (fun a b : α => if a=b then z else 0) f w = z^w.length * f w := by
  induction w generalizing f with
  | nil => simp
  | cons a w ih =>
    rw [reparam_cons]
    simp only [ite_mul, zero_mul, sum_ite_eq', mem_univ, ↓reduceIte]
    rw [ih]
    simp [deriv_apply, pow_succ, mul_assoc, mul_left_comm]
 theorem reparam_scalar_quadratic (z : ℂ) :
    reparam (fun a b : α => if a=b then z else 0) quadratic = z^2 • quadratic := by
  funext w
  rw [reparam_scalar]
  cases w with
  | nil => simp
  | cons a w =>
    cases w with
    | nil => simp [quadratic]
    | cons b w => cases w <;> simp [quadratic]

 theorem Cyclic.append {α : Type} [DecidableEq α] [Fintype α] {f : Series α} (hf : Cyclic f) (u v : List α) :
    f (u++v) = f (v++u) := by
  induction u generalizing v with
  | nil => simp
  | cons a u ih =>
    have hh := congrFun (hf a) (u++v)
    change f (a::(u++v)) = f ((u++v)++[a]) at hh
    simp only [List.cons_append, hh, List.append_assoc]
    rw [ih]
    simp
 theorem cyclic_quadratic {α : Type} [DecidableEq α] [Fintype α] : Cyclic (quadratic : Series α) := by
  intro a
  funext w
  cases w with
  | nil => rfl
  | cons b w =>
    cases w with
    | nil => simp [deriv, rightDeriv, quadratic, eq_comm]
    | cons d w => cases w <;> rfl
 theorem deriv_moments {α : Type} [DecidableEq α] [Fintype α] {R : Series α} (hR : R [] = 0) (i : α) :
    deriv i (moments R) = conv (moments R) (subst (moments R) (deriv i R)) := by
  funext w
  have hh := congrFun (moments_eq hR) (i::w)
  simpa [subst_cons] using hh

end FiniteEntropySeparation.FreeSeries

end

end OAI
