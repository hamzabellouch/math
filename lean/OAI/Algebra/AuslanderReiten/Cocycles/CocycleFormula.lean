import OAI.Algebra.AuslanderReiten.Cocycles.SparseCocycle
import OAI.Algebra.AuslanderReiten.Cocycles.CocycleDifferential
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Tactic.Module

namespace OAI

noncomputable section

namespace ArExplicit.CocycleData

variable {α β k : Type*} [Field k] (q : k)

def evalQuad (a b c d : T k q) (m : QuadMonomial) : T k q :=
  (q ^ m.degree * T.coefficient q m.first a * T.coefficient q m.second b *
    T.coefficient q m.third c * T.coefficient q m.fourth d) • T.vector q m.output

private theorem list_mul_sum (r : k) (l : List α) (f : α → k) :
    r * (l.map f).sum = (l.map fun x => r * f x).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [mul_add, ih]

private theorem list_sum_mul (r : k) (l : List α) (f : α → k) :
    (l.map f).sum * r = (l.map fun x => f x * r).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [add_mul, ih]

private theorem list_sum_map_add {M : Type*} [AddCommMonoid M]
    (l : List α) (f g : α → M) :
    (l.map f).sum + (l.map g).sum = (l.map fun a => f a + g a).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [← ih, add_assoc, add_left_comm]

private theorem list_sum_flatMap {M : Type*} [AddCommMonoid M]
    (l : List α) (f : α → List β) (g : β → M) :
    ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

theorem row_differential (p : TripleMonomial) (a b c d : T k q) :
    a * evalTriple q b c d p + evalTriple q (a * b) c d p +
      evalTriple q a (b * c) d p + evalTriple q a b (c * d) p +
      evalTriple q a b c p * d =
        ((multiplication.flatMap (contributions p)).map (evalQuad q a b c d)).sum := by
  rw [list_sum_flatMap]
  simp only [evalTriple, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  rw [multiplication_eq q a (T.vector q p.output),
    multiplication_eq q (T.vector q p.output) d]
  simp only [multiplication_coefficient, multiplicationCoefficient,
    List.smul_sum, List.sum_smul, list_mul_sum, list_sum_mul, List.map_map, Function.comp_def]
  simp only [list_sum_map_add]
  congr 1
  apply List.map_congr_left
  intro m hm
  simp only [contributions, List.map_append, List.sum_append, evalMul, T.coefficient_vector, smul_smul]
  split_ifs <;> simp_all [evalQuad, pow_add] <;> module

private theorem list_left_mul (a : T k q) (l : List α) (f : α → T k q) :
    a * (l.map f).sum = (l.map fun x => a * f x).sum := by
  induction l with
  | nil => simp
  | cons b l ih => simp [mul_add, ih]

private theorem list_right_mul (a : T k q) (l : List α) (f : α → T k q) :
    (l.map f).sum * a = (l.map fun x => f x * a).sum := by
  induction l with
  | nil => simp
  | cons b l ih => simp [add_mul, ih]

theorem p_differential_formula (a b c d : T k q) :
    a * p q b c d + p q (a * b) c d + p q a (b * c) d +
      p q a b (c * d) + p q a b c * d =
        (differentialTerms.map (evalQuad q a b c d)).sum := by
  simp only [p_apply, list_left_mul, list_right_mul, list_sum_map_add]
  simp_rw [row_differential]
  exact (list_sum_flatMap cochain (fun p => multiplication.flatMap (contributions p))
    (evalQuad q a b c d)).symm

end ArExplicit.CocycleData

end

end OAI
