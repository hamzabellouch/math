import OAI.Analysis.FreeEntropy.CyclicSeries

namespace OAI

universe u1

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α β γ : Type} [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β]

def reparam (c : α → β → ℂ) (f : Series α) : Series β
  | [] => f []
  | b::w => ∑ a, c a b * reparam c (deriv a f) w
@[simp] theorem reparam_nil {α β : Type} [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β] (c : α → β → ℂ) (f : Series α) : reparam c f [] = f [] := rfl
 theorem reparam_cons {α β : Type} [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β] (c : α → β → ℂ) (f : Series α) (b : β) (w : List β) :
    reparam c f (b::w) = ∑ a, c a b * reparam c (deriv a f) w := rfl
 theorem deriv_reparam {α β : Type} [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β] (c : α → β → ℂ) (f : Series α) (b : β) :
    deriv b (reparam c f) = ∑ a, c a b • reparam c (deriv a f) := by
  funext w; simp [deriv_apply, reparam_cons]
 theorem reparam_add {α β : Type} [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β] (c : α → β → ℂ) (f g : Series α) :
    reparam c (f+g) = reparam c f + reparam c g := by
  funext w
  induction w generalizing f g with
  | nil => rfl
  | cons b w ih =>
    simp only [reparam_cons, Pi.add_apply,
      show ∀ a, deriv a (f+g) = deriv a f + deriv a g from fun _ => rfl, ih]
    simp [mul_add, sum_add_distrib]
 theorem reparam_smul {α β : Type} [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β] (c : α → β → ℂ) (z : ℂ) (f : Series α) :
    reparam c (z • f) = z • reparam c f := by
  funext w
  induction w generalizing f with
  | nil => rfl
  | cons b w ih =>
    simp only [reparam_cons, Pi.smul_apply, smul_eq_mul,
      show ∀ a, deriv a (z • f) = z • deriv a f from fun _ => rfl, ih]
    simp [mul_left_comm, mul_sum]
@[simp] theorem reparam_zero (c : α → β → ℂ) : reparam c 0 = 0 := by
  simpa using reparam_smul c 0 0
 theorem reparam_sum {δ : Type u1} (s : Finset δ) (c : α → β → ℂ) (f : δ → Series α) :
    reparam c (∑ d ∈ s, f d) = ∑ d ∈ s, reparam c (f d) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert d s hd ih => simp [sum_insert hd, reparam_add, ih]
@[simp] theorem reparam_unit (c : α → β → ℂ) : reparam c unit = unit := by
  funext w
  cases w with
  | nil => rfl
  | cons b w =>
    have hh (a : α) : deriv a (unit : Series α) = 0 := rfl
    simp [reparam_cons, hh]
 theorem reparam_conv (c : α → β → ℂ) (f g : Series α) :
    reparam c (conv f g) = conv (reparam c f) (reparam c g) := by
  funext w
  induction w generalizing f g with
  | nil => rfl
  | cons b w ih =>
    simp only [reparam_cons, deriv_conv, reparam_add, reparam_smul, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, ih, mul_add, sum_add_distrib]
    rw [conv_cons, reparam_nil, reparam_cons, deriv_reparam, conv_sum_left]
    simp only [conv_smul_left, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    congr 1
    simp [mul_left_comm, mul_sum]
 theorem rightDeriv_reparam {α β : Type} [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β] (c : α → β → ℂ) (f : Series α) (b : β) :
    rightDeriv b (reparam c f) = ∑ a, c a b • reparam c (rightDeriv a f) := by
  funext w
  induction w generalizing f with
  | nil => simp [rightDeriv, reparam_cons]
  | cons d w ih =>
    simp only [rightDeriv_apply, List.cons_append, reparam_cons, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    have hh (a : α) : reparam c (deriv a f) (w++[b]) =
        ∑ j, c j b * reparam c (rightDeriv j (deriv a f)) w := by
      simpa only [rightDeriv_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using ih (deriv a f)
    simp_rw [hh, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro j _
    have he : rightDeriv a (deriv j f) = deriv j (rightDeriv a f) := rfl
    rw [he]
    ring
 theorem Cyclic.reparam {f : Series α} (hf : Cyclic f) (c : α → β → ℂ) :
    Cyclic (reparam c f) := by
  intro b
  rw [deriv_reparam, rightDeriv_reparam]
  apply sum_congr rfl
  intro a _
  rw [hf a]
 theorem reparam_subst (c : α → β → ℂ) (M f : Series α) :
    reparam c (subst M f) = subst (reparam c M) (reparam c f) := by
  funext w
  induction w using length_induction generalizing f with
  | h w ih =>
    cases w with
    | nil => simp
    | cons b w =>
      rw [reparam_cons, subst_cons, deriv_reparam, subst_sum, conv_sum_right]
      simp only [deriv_subst, reparam_conv, subst_smul, conv_smul_right,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      apply sum_congr rfl
      intro a _
      congr 1
      apply conv_agree (n := w.length) (Agree.refl _ _) (fun v hv => ?_) w le_rfl
      exact ih v (by simp; omega) (deriv a f)
 theorem reparam_moments (c : α → β → ℂ) {R : Series α} (hR : R [] = 0) :
    reparam c (moments R) = moments (reparam c R) := by
  apply moments_unique (by simpa using hR)
  have hh := congrArg (reparam c) (moments_eq hR)
  simpa only [reparam_add, reparam_unit, reparam_subst] using hh
 theorem reparam_cumulants (c : α → β → ℂ) {M : Series α} (hM : M [] = 1) :
    reparam c (cumulants M) = cumulants (reparam c M) := by
  apply cumulants_unique (by simpa using hM)
  have hh := congrArg (reparam c) (cumulants_equation hM)
  simpa only [reparam_add, reparam_unit, reparam_subst] using hh

def restrict (e : β → α) (f : Series α) : Series β := fun w => f (w.map e)
 theorem restrict_conv {α β : Type} [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β] (e : β → α) (f g : Series α) :
    restrict e (conv f g) = conv (restrict e f) (restrict e g) := by
  funext w
  simp only [restrict, conv_sum_splits, List.length_map, ← List.map_take, ← List.map_drop]
 theorem restrict_subst (e : β → α) (M f : Series α) :
    restrict e (subst M f) = subst (restrict e M) (restrict e f) := by
  funext w
  induction w using length_induction generalizing f with
  | h w ih =>
    cases w with
    | nil => simp [restrict]
    | cons b w =>
      change subst M f (e b :: w.map e) = _
      rw [subst_cons, subst_cons]
      change restrict e (conv M (subst M (deriv (e b) f))) w = _
      rw [restrict_conv]
      apply conv_agree (n := w.length) (Agree.refl _ _) (fun v hv => ?_) w le_rfl
      exact ih v (by simp; omega) (deriv (e b) f)
 theorem restrict_moments (e : β → α) {R : Series α} (hR : R [] = 0) :
    restrict e (moments R) = moments (restrict e R) := by
  apply moments_unique (show (restrict e R) [] = 0 from hR)
  funext w
  have hh := congrFun (moments_eq hR) (w.map e)
  simp only [Pi.add_apply] at hh
  change moments R (w.map e) = _
  rw [hh]
  congr 1
  · cases w <;> rfl
  · exact congrFun (restrict_subst e _ _) w
end FiniteEntropySeparation.FreeSeries

end

end OAI
