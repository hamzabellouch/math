import OAI.NumberTheory.DukePrimeDegree.Dynamics.LatticeCentralizer
import Mathlib.Data.Matrix.Block

namespace OAI

/-!
# Rational fixed vectors of matrix families

The common fixed-vector space of rational matrices is spanned by rational
fixed vectors. This follows from rationality of matrix centralizers by
adding one trivial coordinate.
-/

noncomputable section
open Matrix Set Module
open scoped Classical

namespace DukePrimeDegree

def rationalVectorCast {n : ℕ} : (Fin n → ℚ) →ₗ[ℚ] (Fin n → ℝ) :=
  (Algebra.linearMap ℚ ℝ).compLeft (Fin n)

@[simp] lemma rationalVectorCast_apply {n : ℕ} (v : Fin n → ℚ) (i : Fin n) :
    rationalVectorCast v i = (v i : ℝ) := rfl

lemma rationalVectorCast_vecMul {n : ℕ} (v : Fin n → ℚ)
    (B : Matrix (Fin n) (Fin n) ℚ) :
    rationalVectorCast (v ᵥ* B) = rationalVectorCast v ᵥ* rationalMatrixCast B := by
  funext i
  exact RingHom.map_vecMul (algebraMap ℚ ℝ) B v i

private def trivialCoordinateExtension {K : Type*} [Field K] {n : ℕ}
    (B : Matrix (Fin n) (Fin n) K) : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) K :=
  Matrix.fromBlocks B 0 0 1

private def fixedRowMatrix {K : Type*} [Field K] {n : ℕ}
    (v : Fin n → K) : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) K :=
  Matrix.fromBlocks 0 0 (Matrix.of (fun (_ : Unit) i => v i)) 0

private lemma fixedRowMatrix_commute {K : Type*} [Field K] {n : ℕ}
    (v : Fin n → K) (B : Matrix (Fin n) (Fin n) K) (hv : v ᵥ* B = v) :
    Commute (fixedRowMatrix v) (trivialCoordinateExtension B) := by
  change fixedRowMatrix v * trivialCoordinateExtension B =
    trivialCoordinateExtension B * fixedRowMatrix v
  unfold fixedRowMatrix trivialCoordinateExtension
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, Matrix.one_mul]
  congr 1
  ext u i
  exact congrFun hv i

private lemma fixedRow_of_commute {K : Type*} [Field K] {n : ℕ}
    (M : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) K)
    (B : Matrix (Fin n) (Fin n) K) (hM : Commute M (trivialCoordinateExtension B)) :
    (fun i => M (Sum.inr ()) (Sum.inl i)) ᵥ* B = fun i => M (Sum.inr ()) (Sum.inl i) := by
  funext i
  have he := congrArg (fun A : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) K =>
    A (Sum.inr ()) (Sum.inl i)) hM.eq
  simpa [Matrix.mul_apply, trivialCoordinateExtension, Matrix.fromBlocks,
    Fintype.sum_sum_type, Matrix.vecMul, dotProduct] using he

private lemma rationalMatrixCast_trivialCoordinateExtension {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℚ) :
    rationalMatrixCast (trivialCoordinateExtension B) =
      trivialCoordinateExtension (rationalMatrixCast B) := by
  ext i j
  cases i <;> cases j <;>
    simp [rationalMatrixCast_apply, trivialCoordinateExtension, Matrix.fromBlocks]

/-- A common real fixed vector is a real linear combination of common
rational fixed vectors of the same actual matrix family. -/
theorem fixedVector_mem_span_rational {n : ℕ} {κ : Type*}
    (B : κ → Matrix (Fin n) (Fin n) ℚ) (v : Fin n → ℝ)
    (hv : ∀ k, v ᵥ* rationalMatrixCast (B k) = v) :
    v ∈ Submodule.span ℝ
      (rationalVectorCast '' {q : Fin n → ℚ | ∀ k, q ᵥ* B k = q}) := by
  let C := fun k => trivialCoordinateExtension (B k)
  let W := Submodule.span ℝ
    (rationalVectorCast '' {q : Fin n → ℚ | ∀ k, q ᵥ* B k = q})
  have hm : fixedRowMatrix v ∈ Submodule.span ℝ
      (rationalMatrixCast '' ((commutatorFamily C).ker :
        Set (Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℚ))) := by
    rw [← real_commutant_eq_span_rational_family C]
    apply (mem_commutatorFamily_ker _ _).mpr
    intro k
    rw [rationalMatrixCast_trivialCoordinateExtension]
    exact fixedRowMatrix_commute v _ (hv k)
  have hproject (M : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ)
      (hM : M ∈ Submodule.span ℝ
        (rationalMatrixCast '' ((commutatorFamily C).ker :
          Set (Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℚ)))) :
      (fun i => M (Sum.inr ()) (Sum.inl i)) ∈ W := by
    induction hM using Submodule.span_induction with
    | mem M hM =>
      obtain ⟨N, hN, rfl⟩ := hM
      apply Submodule.subset_span
      refine ⟨fun i => N (Sum.inr ()) (Sum.inl i), ?_, rfl⟩
      intro k
      exact fixedRow_of_commute N (B k) ((mem_commutatorFamily_ker C N).mp hN k)
    | zero => exact W.zero_mem
    | add M N _ _ hM hN => exact W.add_mem hM hN
    | smul a M _ hM => exact W.smul_mem a hM
  exact hproject _ hm

theorem exists_nonzero_rational_fixedVector {n : ℕ} {κ : Type*}
    (B : κ → Matrix (Fin n) (Fin n) ℚ) (v : Fin n → ℝ) (hv0 : v ≠ 0)
    (hv : ∀ k, v ᵥ* rationalMatrixCast (B k) = v) :
    ∃ q : Fin n → ℚ, q ≠ 0 ∧ ∀ k, q ᵥ* B k = q := by
  have hspan := fixedVector_mem_span_rational B v hv
  by_contra hnone
  have hz : ∀ q : Fin n → ℚ, (∀ k, q ᵥ* B k = q) → q = 0 := by
    intro q hq
    by_contra hq0
    exact hnone ⟨q, hq0, hq⟩
  have hbot : Submodule.span ℝ
      (rationalVectorCast '' {q : Fin n → ℚ | ∀ k, q ᵥ* B k = q}) = ⊥ := by
    apply Submodule.span_eq_bot.mpr
    rintro _ ⟨q, hq, rfl⟩
    simp only [hz q hq, map_zero]
  rw [hbot, Submodule.mem_bot] at hspan
  exact hv0 hspan

end DukePrimeDegree

end

end OAI
