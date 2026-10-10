import OAI.Algebra.AuslanderReiten.Algebras.TMultiplication
import OAI.Algebra.AuslanderReiten.Cocycles.SparseParity

namespace OAI

noncomputable section

namespace ArExplicit.CocycleData

variable {k : Type*} [Field k] (q : k)

def evalMul (a b : T k q) (m : MulMonomial) : T k q :=
  (q ^ m.degree * T.coefficient q m.first a * T.coefficient q m.second b) • T.vector q m.output

theorem multiplication_eq (a b : T k q) :
    a * b = (multiplication.map (evalMul q a b)).sum := by
  apply T.coordinate_ext q
  intro i
  rw [multiplication_coefficient]
  rw [map_list_sum]
  simp [multiplicationCoefficient, evalMul, List.map_map, Function.comp_def, mul_ite, eq_comm]

theorem linearMap_list_sum_apply {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (l : List (M →ₗ[R] N)) (a : M) : l.sum a = (l.map (fun f => f a)).sum := by
  induction l with
  | nil => rfl
  | cons f l ih => simp [List.sum_cons, ih]

def TripleMonomial.linear (p : TripleMonomial) :
    T k q →ₗ[k] T k q →ₗ[k] T k q →ₗ[k] T k q :=
  (T.coefficient q p.first).smulRight
    ((T.coefficient q p.second).smulRight
      ((T.coefficient q p.third).smulRight (q ^ p.degree • T.vector q p.output)))

def evalTriple (a b c : T k q) (p : TripleMonomial) : T k q :=
  (q ^ p.degree * T.coefficient q p.first a * T.coefficient q p.second b *
    T.coefficient q p.third c) • T.vector q p.output

theorem TripleMonomial.linear_apply (p : TripleMonomial) (a b c : T k q) :
    p.linear q a b c = evalTriple q a b c p := by
  simp [TripleMonomial.linear, evalTriple, smul_smul]
  congr 1
  ring

def p : T k q →ₗ[k] T k q →ₗ[k] T k q →ₗ[k] T k q :=
  (cochain.map (TripleMonomial.linear q)).sum

theorem p_apply (a b c : T k q) : p q a b c = (cochain.map (evalTriple q a b c)).sum := by
  simp only [p, linearMap_list_sum_apply, List.map_map, Function.comp_def, TripleMonomial.linear_apply]

theorem basis_evaluation (a b c : TIndex) :
    p q (T.vector q a) (T.vector q b) (T.vector q c) =
      ((cochain.filter fun t => decide (t.first = a ∧ t.second = b ∧ t.third = c)).map
        fun t => q ^ t.degree • T.vector q t.output).sum := by
  rw [p_apply]
  generalize cochain = l
  induction l with
  | nil => rfl
  | cons t l ih =>
    by_cases h1 : t.first = a <;> by_cases h2 : t.second = b <;> by_cases h3 : t.third = c <;>
      simp [evalTriple, h1, h2, h3, ih]

theorem p_txJ : p q (T.vector q (false, .t)) (T.vector q (false, .x))
    (T.vector q (true, .j)) = 0 := by
  rw [basis_evaluation]
  have h : (cochain.filter fun p => decide (p.first = (false, .t) ∧
      p.second = (false, .x) ∧ p.third = (true, .j))) = [] := by decide +kernel
  rw [h]
  rfl

theorem p_tyJ : p q (T.vector q (false, .t)) (T.vector q (false, .y))
    (T.vector q (true, .j)) = q ^ 3 • T.vector q (false, .f) := by
  rw [basis_evaluation]
  have h : (cochain.filter fun p => decide (p.first = (false, .t) ∧
      p.second = (false, .y) ∧ p.third = (true, .j))) =
        [⟨(false, .t), (false, .y), (true, .j), (false, .f), 3⟩] := by decide +kernel
  rw [h]
  simp

theorem p_detecting_cycle :
    q ^ 2 • p q (T.vector q (false, .t)) (T.vector q (false, .x)) (T.vector q (true, .j)) +
      p q (T.vector q (false, .t)) (T.vector q (false, .y)) (T.vector q (true, .j)) =
        q ^ 3 • T.vector q (false, .f) := by
  rw [p_txJ, p_tyJ, smul_zero, zero_add]

end ArExplicit.CocycleData

end

end OAI
