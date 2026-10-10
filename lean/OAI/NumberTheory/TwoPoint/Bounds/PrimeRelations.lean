import OAI.NumberTheory.TwoPoint.Bounds.TriangularElimination

namespace OAI

/-!
# Exact prime-variable relations

A monomial has one factor for each distinct label in a squarefree tuple.
Its integer coefficient contains the orientation, common shift multiplier,
and padding. Numerical coincidences among different labels are allowed.
-/

namespace TwoPointCorrelations

open Finset

structure PrimeMonomial (ι : Type*) where
  coefficient : ℤ
  labels : Finset ι

namespace PrimeMonomial

variable {ι : Type*} [DecidableEq ι]

def eval (m : PrimeMonomial ι) (x : ι → ℤ) : ℤ :=
  m.coefficient * ∏ j ∈ m.labels, x j

def coefficientAt (m : PrimeMonomial ι) (i : ι) (x : ι → ℤ) : ℤ :=
  if i ∈ m.labels then m.coefficient * ∏ j ∈ m.labels.erase i, x j else 0

def constantAt (m : PrimeMonomial ι) (i : ι) (x : ι → ℤ) : ℤ :=
  if i ∈ m.labels then 0 else m.eval x

lemma eval_affine (m : PrimeMonomial ι) (i : ι) (x : ι → ℤ) :
    m.eval x = x i * m.coefficientAt i x + m.constantAt i x := by
  by_cases hi : i ∈ m.labels
  · simp only [eval, coefficientAt, constantAt, hi, ite_true, add_zero]
    rw [← Finset.mul_prod_erase m.labels x hi]
    ring
  · simp only [coefficientAt, constantAt, hi, ite_false, mul_zero, zero_add]

lemma eval_update_of_not_mem (m : PrimeMonomial ι) (i : ι) (x : ι → ℤ) (a : ℤ)
    (hi : i ∉ m.labels) : m.eval (Function.update x i a) = m.eval x := by
  unfold eval
  congr 1
  apply prod_congr rfl
  intro j hj
  have hji : j ≠ i := fun h => hi (h ▸ hj)
  simp [hji]

lemma coefficientAt_update_self (m : PrimeMonomial ι) (i : ι) (x : ι → ℤ) (a : ℤ) :
    m.coefficientAt i (Function.update x i a) = m.coefficientAt i x := by
  unfold coefficientAt
  split
  · congr 1
    apply prod_congr rfl
    intro j hj
    simp [(mem_erase.mp hj).1]
  · rfl

lemma constantAt_update_self (m : PrimeMonomial ι) (i : ι) (x : ι → ℤ) (a : ℤ) :
    m.constantAt i (Function.update x i a) = m.constantAt i x := by
  unfold constantAt
  split
  · rfl
  · exact m.eval_update_of_not_mem i x a ‹i ∉ m.labels›

lemma coefficientAt_update_of_not_mem (m : PrimeMonomial ι) (i j : ι)
    (x : ι → ℤ) (a : ℤ) (hj : j ∉ m.labels) :
    m.coefficientAt i (Function.update x j a) = m.coefficientAt i x := by
  unfold coefficientAt
  split
  · congr 1
    apply prod_congr rfl
    intro k hk
    have hkj : k ≠ j := fun h => hj (h ▸ (mem_erase.mp hk).2)
    simp [hkj]
  · rfl

end PrimeMonomial

variable {ι τ : Type*} [DecidableEq ι] [Fintype τ]

def primeRelationEval (m : τ → PrimeMonomial ι) (x : ι → ℤ) : ℤ := ∑ t, (m t).eval x

def primeRelationCoefficient (m : τ → PrimeMonomial ι) (i : ι) (x : ι → ℤ) : ℤ :=
  ∑ t, (m t).coefficientAt i x

def primeRelationConstant (m : τ → PrimeMonomial ι) (i : ι) (x : ι → ℤ) : ℤ :=
  ∑ t, (m t).constantAt i x

/-- The contribution of precisely the terms containing this label. -/
def primeRelationContribution (m : τ → PrimeMonomial ι) (i : ι) (x : ι → ℤ) : ℤ :=
  ∑ t, if i ∈ (m t).labels then (m t).eval x else 0

def primeRelationSupport (m : τ → PrimeMonomial ι) : Finset ι := univ.biUnion (fun t => (m t).labels)

lemma primeRelation_affine (m : τ → PrimeMonomial ι) (i : ι) (x : ι → ℤ) :
    primeRelationEval m x = x i * primeRelationCoefficient m i x + primeRelationConstant m i x := by
  unfold primeRelationEval primeRelationCoefficient primeRelationConstant
  rw [mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro t _
  exact (m t).eval_affine i x

lemma primeRelation_contribution_eq (m : τ → PrimeMonomial ι) (i : ι) (x : ι → ℤ) :
    primeRelationContribution m i x = x i * primeRelationCoefficient m i x := by
  unfold primeRelationContribution primeRelationCoefficient
  rw [mul_sum]
  apply sum_congr rfl
  intro t _
  by_cases hi : i ∈ (m t).labels
  · rw [ite_eq_left hi, (m t).eval_affine i x]
    simp only [PrimeMonomial.constantAt, hi, ite_true, add_zero]
  · simp only [hi, ite_false, PrimeMonomial.coefficientAt, mul_zero]

lemma primeRelation_coefficient_update_self (m : τ → PrimeMonomial ι)
    (i : ι) (x : ι → ℤ) (a : ℤ) :
    primeRelationCoefficient m i (Function.update x i a) = primeRelationCoefficient m i x := by
  unfold primeRelationCoefficient
  exact sum_congr rfl (fun t _ => (m t).coefficientAt_update_self i x a)

lemma primeRelation_constant_update_self (m : τ → PrimeMonomial ι)
    (i : ι) (x : ι → ℤ) (a : ℤ) :
    primeRelationConstant m i (Function.update x i a) = primeRelationConstant m i x := by
  unfold primeRelationConstant
  exact sum_congr rfl (fun t _ => (m t).constantAt_update_self i x a)

lemma primeRelation_update_affine (m : τ → PrimeMonomial ι)
    (i : ι) (x : ι → ℤ) (a : ℤ) :
    primeRelationEval m (Function.update x i a) =
      a * primeRelationCoefficient m i x + primeRelationConstant m i x := by
  rw [primeRelation_affine m i, Function.update_self,
    primeRelation_coefficient_update_self, primeRelation_constant_update_self]

lemma primeRelation_update_of_not_mem (m : τ → PrimeMonomial ι)
    (i : ι) (x : ι → ℤ) (a : ℤ) (hi : i ∉ primeRelationSupport m) :
    primeRelationEval m (Function.update x i a) = primeRelationEval m x := by
  unfold primeRelationEval
  apply sum_congr rfl
  intro t _
  apply (m t).eval_update_of_not_mem
  exact fun hit => hi (mem_biUnion.mpr ⟨t, mem_univ _, hit⟩)

lemma primeRelation_coefficient_update_of_not_mem (m : τ → PrimeMonomial ι)
    (i j : ι) (x : ι → ℤ) (a : ℤ) (hj : j ∉ primeRelationSupport m) :
    primeRelationCoefficient m i (Function.update x j a) = primeRelationCoefficient m i x := by
  unfold primeRelationCoefficient
  apply sum_congr rfl
  intro t _
  apply (m t).coefficientAt_update_of_not_mem
  exact fun hjt => hj (mem_biUnion.mpr ⟨t, mem_univ _, hjt⟩)

/-- Retaining the nonzero-contribution test gives precisely the coefficient
condition needed for a single-prime reciprocal saving. -/
lemma primeRelation_coefficient_nondegenerate (m : τ → PrimeMonomial ι)
    (i : ι) (x : ι → ℤ) (p : ℤ)
    (hnonzero : ¬p ∣ primeRelationContribution m i x) :
    ¬p ∣ primeRelationCoefficient m i x := by
  intro hd
  apply hnonzero
  rw [primeRelation_contribution_eq]
  exact hd.mul_left (x i)

/-- The whole congruence, including its nondegeneracy test and controlling
prime, ignores a variable outside the recorded support and control. -/
def primeRelationEvent (m : τ → PrimeMonomial ι) (selected control : ι) (x : ι → ℤ) : Prop :=
  x control ∣ primeRelationEval m x ∧ ¬x control ∣ primeRelationCoefficient m selected x

lemma primeRelationEvent_update (m : τ → PrimeMonomial ι) (selected control j : ι)
    (x : ι → ℤ) (a : ℤ) (hj : j ∉ primeRelationSupport m) (hjc : control ≠ j) :
    primeRelationEvent m selected control (Function.update x j a) ↔
      primeRelationEvent m selected control x := by
  unfold primeRelationEvent
  rw [Function.update_of_ne hjc, primeRelation_update_of_not_mem m j x a hj,
    primeRelation_coefficient_update_of_not_mem m selected j x a hj]

end TwoPointCorrelations

end OAI
