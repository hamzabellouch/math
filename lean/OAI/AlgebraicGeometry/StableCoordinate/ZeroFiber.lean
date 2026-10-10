import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace OAI

/-!
# The zero-fiber elimination

The quotient by the specialized defining equation of Section 2 is a polynomial
algebra in three independent variables.  The construction is an algebra
isomorphism, not merely a bijection on points, and works over any commutative
coefficient ring.
-/

noncomputable section

namespace StableCoordinate.ZeroFiber

open MvPolynomial

variable (K : Type*) [CommRing K]

abbrev Four := MvPolynomial (Fin 4) K
abbrev Three := MvPolynomial (Fin 3) K

def squareDifference : Four K := X 0 ^ 2 - X 1 ^ 2

def relation : Four K :=
  squareDifference K ^ 2 * X 2 - (1 + 2 * X 0 * squareDifference K) * X 3 - X 1

def relationIdeal : Ideal (Four K) := Ideal.span {relation K}

abbrev Ring := Four K ⧸ relationIdeal K

def qmk : Four K →ₐ[K] Ring K := Ideal.Quotient.mkₐ K _

def forward : Four K →ₐ[K] Three K :=
  aeval ![X 0, X 1,
    4 * X 0 ^ 2 * X 1 + (1 + 2 * X 0 * (X 0 ^ 2 - X 1 ^ 2)) * X 2,
    -(1 - 2 * X 0 * (X 0 ^ 2 - X 1 ^ 2)) * X 1 + (X 0 ^ 2 - X 1 ^ 2) ^ 2 * X 2]

lemma forward_relation : forward K (relation K) = 0 := by
  simp only [forward, relation, squareDifference, map_sub, map_add, map_mul, map_pow,
    map_ofNat, aeval_X, map_one]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  ring

lemma forward_vanishes : ∀ a ∈ relationIdeal K, forward K a = 0 := by
  intro a ha
  have h : relationIdeal K ≤ RingHom.ker (forward K).toRingHom := by
    rw [relationIdeal, Ideal.span_le]
    intro b hb
    rcases Set.mem_singleton_iff.mp hb with rfl
    exact forward_relation K
  exact h ha

def toThree : Ring K →ₐ[K] Three K :=
  Ideal.Quotient.liftₐ _ (forward K) (forward_vanishes K)

@[simp] lemma toThree_qmk (a : Four K) : toThree K (qmk K a) = forward K a := rfl

def backward : Three K →ₐ[K] Ring K :=
  aeval ![qmk K (X 0), qmk K (X 1),
    qmk K ((1 - 2 * X 0 * squareDifference K) * X 2 + 4 * X 0 ^ 2 * X 3)]

lemma forward_backward : (toThree K).comp (backward K) = AlgHom.id K (Three K) := by
  ext i : 1
  fin_cases i <;> simp [backward, forward, squareDifference, map_ofNat]
  ring

lemma qmk_relation : qmk K (relation K) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (Set.mem_singleton _)

lemma backward_forward : (backward K).comp (toThree K) = AlgHom.id K (Ring K) := by
  apply Ideal.Quotient.algHom_ext
  ext i : 1
  change backward K (toThree K (qmk K (X i))) = qmk K (X i)
  rw [toThree_qmk]
  fin_cases i <;> simp [forward, backward, map_ofNat]
  · have h := qmk_relation K
    simp only [relation, squareDifference, map_sub, map_add, map_mul, map_pow,
      map_ofNat, map_one] at h ⊢
    linear_combination -4 * (qmk K (X 0)) ^ 2 * h
  · have h := qmk_relation K
    simp only [relation, squareDifference, map_sub, map_add, map_mul, map_pow,
      map_ofNat, map_one] at h ⊢
    linear_combination (1 - 2 * qmk K (X 0) * (qmk K (X 0) ^ 2 - qmk K (X 1) ^ 2)) * h

/-- The zero fiber of the five-generator hypersurface presentation is affine
three-space, expressed by an isomorphism of coordinate algebras. -/
def presentationEquiv : Ring K ≃ₐ[K] Three K :=
  AlgEquiv.ofAlgHom (toThree K) (backward K) (forward_backward K) (backward_forward K)

end StableCoordinate.ZeroFiber

end

end OAI
