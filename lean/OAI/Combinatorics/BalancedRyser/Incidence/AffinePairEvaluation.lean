import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic
import OAI.Combinatorics.BalancedRyser.Incidence.Affine

namespace OAI

namespace Balanced.PairEvaluation

variable {F : Type*} [Field F]

theorem eval_intersection (d e : Direction F) (hde : d ≠ e) (a b : F) :
    (lineEval d (lineIntersection (d, a) (e, b)),
      lineEval e (lineIntersection (d, a) (e, b))) = (a, b) := by
  cases d with
  | none =>
      cases e with
      | none => exact False.elim (hde rfl)
      | some m =>
          apply Prod.ext <;> simp [lineEval, lineIntersection]
  | some m =>
      cases e with
      | none =>
          apply Prod.ext <;> simp [lineEval, lineIntersection]
      | some n =>
          have hmn : m - n ≠ 0 := sub_ne_zero.mpr (fun h => hde (congrArg some h))
          apply Prod.ext
          · simp [lineEval, lineIntersection]
          · simp only [lineEval, lineIntersection]
            field_simp
            ring

theorem intersection_eval (d e : Direction F) (hde : d ≠ e) (p : Point F) :
    lineIntersection (d, lineEval d p) (e, lineEval e p) = p := by
  rcases p with ⟨x, y⟩
  cases d with
  | none =>
      cases e with
      | none => exact False.elim (hde rfl)
      | some m =>
          apply Prod.ext <;> simp [lineEval, lineIntersection]
  | some m =>
      cases e with
      | none =>
          apply Prod.ext <;> simp [lineEval, lineIntersection]
      | some n =>
          have hmn : m - n ≠ 0 := sub_ne_zero.mpr (fun h => hde (congrArg some h))
          have hx : ((y - n * x) - (y - m * x)) / (m - n) = x := by
            apply (div_eq_iff hmn).mpr
            ring
          apply Prod.ext
          · exact hx
          · simp only [lineEval, lineIntersection]
            rw [hx]
            ring

def pairEvalEquiv (d e : Direction F) (hde : d ≠ e) : Point F ≃ F × F where
  toFun p := (lineEval d p, lineEval e p)
  invFun ab := lineIntersection (d, ab.1) (e, ab.2)
  left_inv := intersection_eval d e hde
  right_inv ab := eval_intersection d e hde ab.1 ab.2

@[simp] theorem pairEvalEquiv_apply (d e : Direction F) (hde : d ≠ e) (p : Point F) :
    pairEvalEquiv d e hde p = (lineEval d p, lineEval e p) := rfl

@[simp] theorem pairEvalEquiv_symm_apply (d e : Direction F) (hde : d ≠ e) (a b : F) :
    (pairEvalEquiv d e hde).symm (a, b) = lineIntersection (d, a) (e, b) := rfl

def lineCoordinateEquiv (d e : Direction F) (hde : d ≠ e) (a : F) :
    {p : Point F // OnLine p (d, a)} ≃ F where
  toFun p := lineEval e p.1
  invFun b := ⟨lineIntersection (d, a) (e, b),
    congrArg Prod.fst (eval_intersection d e hde a b)⟩
  left_inv p := by
    apply Subtype.ext
    have hp : lineEval d p.1 = a := p.2
    simpa [hp] using intersection_eval d e hde p.1
  right_inv b := congrArg Prod.snd (eval_intersection d e hde a b)

@[simp] theorem lineCoordinateEquiv_apply (d e : Direction F) (hde : d ≠ e)
    (a : F) (p : {p : Point F // OnLine p (d, a)}) :
    lineCoordinateEquiv d e hde a p = lineEval e p.1 := rfl

theorem existsUnique_eval_pair (d e : Direction F) (hde : d ≠ e) (a b : F) :
    ∃! p : Point F, lineEval d p = a ∧ lineEval e p = b := by
  refine ⟨lineIntersection (d, a) (e, b), ?_, ?_⟩
  · have h := eval_intersection d e hde a b
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · intro p hp
    have h := intersection_eval d e hde p
    simpa [hp.1, hp.2] using h.symm

theorem sum_eval_pair [Fintype F] {A : Type*} [AddCommMonoid A]
    (d e : Direction F) (hde : d ≠ e) (f : F × F → A) :
    (∑ p : Point F, f (lineEval d p, lineEval e p)) = ∑ ab : F × F, f ab := by
  exact Equiv.sum_comp (pairEvalEquiv d e hde) f

end Balanced.PairEvaluation

end OAI
