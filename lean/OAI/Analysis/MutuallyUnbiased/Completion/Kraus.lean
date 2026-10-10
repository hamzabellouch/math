import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Finite trace-preserving Kraus maps

The proof establishes the fixed-point commutation step needed in Weiner's completion
argument. It replaces the appeal to two-positivity and the multiplicative domain
with the squared Hilbert--Schmidt norm of each commutator.
-/

namespace MUB6.Weiner

open scoped BigOperators ComplexOrder
open Matrix

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]

/-- A finite Kraus sum, with the adjoint on the left. -/
def kraus (A : ι → Matrix n n ℂ) (X : Matrix n n ℂ) : Matrix n n ℂ :=
  ∑ i, (A i)ᴴ * X * A i

omit [DecidableEq n] in
lemma kraus_conjTranspose (A : ι → Matrix n n ℂ) (X : Matrix n n ℂ) :
    kraus A Xᴴ = (kraus A X)ᴴ := by
  simp [kraus, conjTranspose_sum, conjTranspose_mul, mul_assoc]

omit [DecidableEq n] in
lemma trace_kraus (A : ι → Matrix n n ℂ) (X : Matrix n n ℂ) :
    (kraus A X).trace = ((∑ i, A i * (A i)ᴴ) * X).trace := by
  simp only [kraus, Matrix.trace_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.trace_mul_comm, Matrix.mul_assoc]

/-- A trace-preserving Kraus sum satisfies the second normalization identity. -/
theorem right_unital_of_trace_preserving (A : ι → Matrix n n ℂ)
    (htrace : ∀ X : Matrix n n ℂ, (kraus A X).trace = X.trace) :
    ∑ i, A i * (A i)ᴴ = 1 := by
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro X
  rw [← trace_kraus, htrace, Matrix.one_mul]

omit [DecidableEq n] in
/-- The trace of the sum of commutator squares. -/
lemma commutator_trace_identity (A : ι → Matrix n n ℂ) (X : Matrix n n ℂ) :
    ∑ i, (((X * A i - A i * X)ᴴ * (X * A i - A i * X)).trace) =
      (Xᴴ * X * (∑ i, A i * (A i)ᴴ)).trace
      + (Xᴴ * (∑ i, (A i)ᴴ * A i) * X).trace
      - (kraus A Xᴴ * X).trace - (Xᴴ * kraus A X).trace := by
  simp only [conjTranspose_sub, conjTranspose_mul]
  simp only [sub_mul, mul_sub, Matrix.trace_sub, Finset.sum_sub_distrib,
    kraus, Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum]
  have h₁ : ∀ i, (((A i)ᴴ * Xᴴ) * (X * A i)).trace =
      ((Xᴴ * X) * (A i * (A i)ᴴ)).trace := by
    intro i
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  simp only [Matrix.mul_assoc] at h₁ ⊢
  simp only [h₁]
  ring

/-- Fixed points of a unital trace-preserving finite Kraus sum commute with its
Kraus operators. The result needs no positivity axioms or external solver. -/
theorem commute_of_kraus_fixed (A : ι → Matrix n n ℂ)
    (hleft : ∑ i, (A i)ᴴ * A i = 1)
    (hright : ∑ i, A i * (A i)ᴴ = 1)
    (X : Matrix n n ℂ) (hX : kraus A X = X) (i : ι) :
    Commute X (A i) := by
  have hstar : kraus A Xᴴ = Xᴴ := by rw [kraus_conjTranspose, hX]
  have hsum : ∑ j, (((X * A j - A j * X)ᴴ * (X * A j - A j * X)).trace) = 0 := by
    rw [commutator_trace_identity, hleft, hright, hX, hstar]
    simp
  have hnonneg : ∀ j ∈ (Finset.univ : Finset ι),
      0 ≤ (((X * A j - A j * X)ᴴ * (X * A j - A j * X)).trace) := by
    intro j _
    exact (Matrix.posSemidef_conjTranspose_mul_self _).trace_nonneg
  have hi := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum i (Finset.mem_univ i)
  exact sub_eq_zero.mp (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp hi)

end MUB6.Weiner

end OAI
