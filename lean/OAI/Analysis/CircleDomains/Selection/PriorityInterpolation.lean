import OAI.Analysis.CircleDomains.Sobolev.LocalComplexWitness
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.Module

namespace OAI

/-! Finite priority interpolation of a horizontal coordinate. Overlaps
of the cutoff supports are allowed; the derivative estimate is uniform
in the number of cutoffs. -/
open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 def priorityBlend : List ((E → ℝ) × ℝ) → (E → ℝ) → E → ℝ
  | [], X => X
  | e :: L, X => fun p => e.1 p*e.2+(1-e.1 p)*priorityBlend L X p

 def priorityResidual : List ((E → ℝ) × ℝ) → E → ℝ
  | [] => fun _ => 1
  | e :: L => fun p => (1-e.1 p)*priorityResidual L p

 omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
 theorem priorityBlend_norm_le {L : List ((E → ℝ) × ℝ)} {X : E → ℝ} {p : E} {B : ℝ}
    (hX : ‖X p‖ ≤ B) (hL : ∀ e ∈ L, e.1 p ∈ Icc (0 : ℝ) 1 ∧ ‖e.2‖ ≤ B) :
    ‖priorityBlend L X p‖ ≤ B := by
  induction L with
  | nil => exact hX
  | cons e L ih =>
    have he := hL e (by simp)
    have ht := ih (fun a ha => hL a (by simp [ha]))
    have h0 : 0 ≤ 1-e.1 p := by linarith [he.1.2]
    calc
      ‖priorityBlend (e::L) X p‖ ≤ ‖e.1 p*e.2‖+‖(1-e.1 p)*priorityBlend L X p‖ := norm_add_le _ _
      _ = e.1 p*‖e.2‖+(1-e.1 p)*‖priorityBlend L X p‖ := by
        simp only [norm_mul, Real.norm_eq_abs (e.1 p), abs_of_nonneg he.1.1,
          Real.norm_eq_abs (1-e.1 p), abs_of_nonneg h0]
      _ ≤ e.1 p*B+(1-e.1 p)*B := add_le_add
        (mul_le_mul_of_nonneg_left he.2 he.1.1) (mul_le_mul_of_nonneg_left ht h0)
      _ = B := by ring

 omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
 theorem priorityResidual_unit {L : List ((E → ℝ) × ℝ)} {p : E}
    (hL : ∀ e ∈ L, e.1 p ∈ Icc (0 : ℝ) 1) : priorityResidual L p ∈ Icc (0 : ℝ) 1 := by
  induction L with
  | nil => simp [priorityResidual]
  | cons e L ih =>
    have he := hL e (by simp)
    have ht := ih (fun a ha => hL a (by simp [ha]))
    have hnonneg : 0 ≤ 1-e.1 p := by linarith [he.2]
    exact ⟨mul_nonneg hnonneg ht.1,
      (mul_le_mul (by linarith [he.1] : 1-e.1 p ≤ 1) ht.2 ht.1 zero_le_one).trans_eq (one_mul 1)⟩

 theorem priorityBlend_differentiableAt {L : List ((E → ℝ) × ℝ)} {X : E → ℝ} {p : E}
    (hX : DifferentiableAt ℝ X p) (hL : ∀ e ∈ L, DifferentiableAt ℝ e.1 p) :
    DifferentiableAt ℝ (priorityBlend L X) p := by
  induction L with
  | nil => exact hX
  | cons e L ih =>
    have he := hL e (by simp)
    exact (he.mul_const e.2).add ((differentiableAt_const 1).sub he |>.mul
      (ih (fun a ha => hL a (by simp [ha]))))

 theorem priorityBlend_derivative_bound {L : List ((E → ℝ) × ℝ)} {X : E → ℝ} {p : E} {B : ℝ}
    (hX : DifferentiableAt ℝ X p) (hXbound : ‖X p‖ ≤ B)
    (hL : ∀ e ∈ L, DifferentiableAt ℝ e.1 p ∧ e.1 p ∈ Icc (0 : ℝ) 1 ∧ ‖e.2‖ ≤ B) :
    ‖fderiv ℝ (priorityBlend L X) p-priorityResidual L p • fderiv ℝ X p‖ ≤
      2*B*(L.map (fun e => ‖fderiv ℝ e.1 p‖)).sum := by
  induction L with
  | nil => simp [priorityBlend, priorityResidual]
  | cons e L ih =>
    have he := hL e (by simp)
    have ht (a) (ha : a ∈ L) := hL a (by simp [ha])
    have htd := priorityBlend_differentiableAt hX (fun a ha => (ht a ha).1)
    have htb := priorityBlend_norm_le hXbound (fun a ha => (ht a ha).2)
    have hdiff := (he.1.hasFDerivAt.mul_const e.2).add
      (((hasFDerivAt_const (1 : ℝ) p).sub he.1.hasFDerivAt).mul htd.hasFDerivAt)
    have hform : fderiv ℝ (priorityBlend (e::L) X) p =
        (e.2-priorityBlend L X p) • fderiv ℝ e.1 p +
          (1-e.1 p) • fderiv ℝ (priorityBlend L X) p := by
      have hdEq := hdiff.fderiv
      change fderiv ℝ (priorityBlend (e::L) X) p = _ at hdEq
      simp only [Pi.sub_apply, zero_sub] at hdEq
      rw [hdEq]
      module
    have herror : fderiv ℝ (priorityBlend (e::L) X) p -
        priorityResidual (e::L) p • fderiv ℝ X p =
        (e.2-priorityBlend L X p) • fderiv ℝ e.1 p + (1-e.1 p) •
          (fderiv ℝ (priorityBlend L X) p-priorityResidual L p • fderiv ℝ X p) := by
      rw [hform]
      dsimp only [priorityResidual]
      module
    have hnonneg : 0 ≤ 1-e.1 p := by linarith [he.2.1.2]
    have hcoef : ‖1-e.1 p‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      linarith [he.2.1.1]
    have hval : ‖e.2-priorityBlend L X p‖ ≤ 2*B :=
      (norm_sub_le _ _).trans (by linarith [he.2.2, htb])
    rw [herror, List.map_cons, List.sum_cons, mul_add]
    calc
      _ ≤ ‖(e.2-priorityBlend L X p) • fderiv ℝ e.1 p‖ +
          ‖(1-e.1 p) • (fderiv ℝ (priorityBlend L X) p-priorityResidual L p • fderiv ℝ X p)‖ :=
        norm_add_le _ _
      _ ≤ 2*B*‖fderiv ℝ e.1 p‖ +
          ‖fderiv ℝ (priorityBlend L X) p-priorityResidual L p • fderiv ℝ X p‖ := by
        simp only [norm_smul]
        exact add_le_add (mul_le_mul_of_nonneg_right hval (norm_nonneg _))
          ((mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)).trans_eq (one_mul _))
      _ ≤ _ := add_le_add le_rfl (ih ht)

end CircleDomainRigidity

end

end OAI
