import OAI.Algebra.AuslanderReiten.Cocycles.TwistedBoundaryData
import OAI.Algebra.AuslanderReiten.Cocycles.CocycleTwist
import Mathlib.Tactic.Module

namespace OAI

noncomputable section

namespace ArExplicit.CocycleData

variable {α β : Type*} {k : Type*} [Field k] (q : k)

def evalPair (H : k) (a b : T k q) (m : PairMonomial) : T k q :=
  (q ^ m.qDegree * H ^ m.hDegree * T.coefficient q m.first a *
    T.coefficient q m.second b) • T.vector q m.output

private theorem list_sum_flatMap {M : Type*} [AddCommMonoid M]
    (l : List α) (f : α → List β) (g : β → M) :
    ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

private theorem list_sum_map_add {M : Type*} [AddCommMonoid M]
    (l : List α) (f g : α → M) :
    (l.map f).sum + (l.map g).sum = (l.map fun a => f a + g a).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [← ih, add_assoc, add_left_comm]

private theorem list_right_mul (a : T k q) (l : List α) (f : α → T k q) :
    (l.map f).sum * a = (l.map fun x => f x * a).sum := by
  induction l with
  | nil => simp
  | cons b l ih => simp [add_mul, ih]

private theorem sum_list_comm {M : Type*} [AddCommMonoid M] {ι : Type*} [Fintype ι]
    (l : List α) (f : ι → α → M) :
    (∑ i, (l.map (f i)).sum) = (l.map fun a => ∑ i, f i a).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [Finset.sum_add_distrib, ih]

theorem row_twisted_contraction (H : kˣ) (t : TripleMonomial) (a b : T k q) :
    (∑ i : TIndex, evalTriple q a b (TrivialExtension.twist H (T.vector q i)) t *
      T.vector q i.star) =
    ((multiplication.flatMap (boundaryLeftContribution t)).map (evalPair q H a b)).sum := by
  rw [Finset.sum_eq_single t.third]
  · simp only [evalTriple, coefficient_twist, T.coefficient_vector]
    rw [Algebra.smul_mul_assoc, multiplication_eq]
    rw [list_sum_flatMap]
    simp only [List.smul_sum, List.map_map, Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro m hm
    simp only [evalMul, T.coefficient_vector, boundaryLeftContribution]
    split_ifs <;> simp_all [evalPair, pow_add, smul_smul]
    all_goals module
  · intro i _ hi
    simp only [evalTriple, coefficient_twist, T.coefficient_vector, ite_eq_right (Ne.symm hi),
      mul_zero, zero_smul, zero_mul]
  · simp

theorem twisted_contraction_formula (H : kˣ) (a b : T k q) :
    (∑ i : TIndex, p q a b (TrivialExtension.twist H (T.vector q i)) * T.vector q i.star) =
      ((cochain.flatMap fun t => multiplication.flatMap (boundaryLeftContribution t)).map
        (evalPair q H a b)).sum := by
  simp only [p_apply, list_right_mul]
  rw [sum_list_comm]
  simp_rw [row_twisted_contraction]
  exact (list_sum_flatMap cochain _ (evalPair q H a b)).symm

private theorem selected_eq (i : TIndex) : selected i = zSelected i := by
  obtain ⟨b, i⟩ := i
  cases b <;> cases i <;> rfl

private theorem mul_inverse_weight (H : kˣ) (i : TIndex) :
    (H : k) * ((H⁻¹ : kˣ) : k) ^ i.weight = (H : k) ^ (if i.1 then 0 else 1) := by
  obtain ⟨b, i⟩ := i
  cases b <;> simp [TIndex.weight]

theorem twisted_boundary_formula (H : kˣ) (a b : T k q) :
    a * z q H b + z q H (a * b) + z q H a * TrivialExtension.twist H⁻¹ b =
      ((multiplication.flatMap boundaryRightContributions).map (evalPair q H a b)).sum := by
  rw [multiplication_eq q a (z q H b), multiplication_eq q a b,
    multiplication_eq q (z q H a) (TrivialExtension.twist H⁻¹ b), map_list_sum]
  simp only [List.map_map, Function.comp_def, evalMul, map_smul, z_vector]
  rw [list_sum_flatMap]
  simp only [list_sum_map_add]
  congr 1
  apply List.map_congr_left
  intro m hm
  simp only [boundaryRightContributions, ← selected_eq, List.map_append, List.sum_append]
  simp only [evalMul, coefficient_z, coefficient_twist]
  have hinv := mul_inverse_weight H m.second
  have he : q ^ m.degree * ((H : k) * q * T.coefficient q m.first a) *
      (((H⁻¹ : kˣ) : k) ^ m.second.weight * T.coefficient q m.second b) =
      q ^ (m.degree + 1) * (H : k) ^ (if m.second.1 then 0 else 1) *
        T.coefficient q m.first a * T.coefficient q m.second b := by
    calc
      _ = ((H : k) * ((H⁻¹ : kˣ) : k) ^ m.second.weight) *
          (q ^ m.degree * q * T.coefficient q m.first a * T.coefficient q m.second b) := by ring
      _ = _ := by rw [hinv, pow_succ]; ring
  split_ifs <;> simp_all [evalPair, pow_succ, smul_smul] <;> module

end ArExplicit.CocycleData

end

end OAI
