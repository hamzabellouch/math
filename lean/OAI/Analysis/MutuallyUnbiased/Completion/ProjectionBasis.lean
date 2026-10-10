import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.LinearAlgebra.Complex.Module
import OAI.Analysis.MutuallyUnbiased.Completion.Superoperator
import OAI.Analysis.MutuallyUnbiased.Completion.JointBasis

namespace OAI

/-!
# Rank-one projectors fixed by a realigned orthogonal projection

The fixed space of the complement operator contains the projectors of an
orthonormal basis. This is the spectral part of the completion argument.
-/

namespace MUB6.Weiner

open Matrix Module
open scoped BigOperators Function

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix of the orthogonal rank-one operator associated with a vector. -/
def projector (v : EuclideanSpace ℂ n) : Matrix n n ℂ :=
  Matrix.vecMulVec v (star v)

lemma toEuclideanLin_projector (v : EuclideanSpace ℂ n) :
    Matrix.toEuclideanLin (projector v) = (InnerProductSpace.rankOne ℂ v v).toLinearMap := by
  rw [projector, ← InnerProductSpace.symm_toEuclideanLin_rankOne]
  exact LinearEquiv.apply_symm_apply _ _

/-- The real and imaginary parts of the reshaped columns. -/
noncomputable def hermitianColumn (C : Matrix (n × n) (n × n) ℂ)
    (p : Bool × (n × n)) : Matrix n n ℂ :=
  if p.1 then (imaginaryPart (superColumn C p.2) : Matrix n n ℂ)
  else (realPart (superColumn C p.2) : Matrix n n ℂ)

omit [Fintype n] [DecidableEq n] in
lemma hermitianColumn_isHermitian (C : Matrix (n × n) (n × n) ℂ)
    (p : Bool × (n × n)) : (hermitianColumn C p).IsHermitian := by
  rcases p with ⟨b, p⟩
  cases b <;> simp only [hermitianColumn, Bool.false_eq_true, ite_false, ite_true]
  · exact Matrix.isHermitian_iff_isSelfAdjoint.mpr (realPart (superColumn C p)).property
  · exact Matrix.isHermitian_iff_isSelfAdjoint.mpr (imaginaryPart (superColumn C p)).property

omit [DecidableEq n] in
lemma hermitianColumn_fixed (C : Matrix (n × n) (n × n) ℂ)
    (hherm : Cᴴ = C) (hidem : C * C = C) (hreal : IsRealigned C)
    (p : Bool × (n × n)) : applySuper C (hermitianColumn C p) = hermitianColumn C p := by
  have hf := superColumn_fixed C hidem p.2
  have hs : applySuper C (superColumn C p.2)ᴴ = (superColumn C p.2)ᴴ := by
    rw [applySuper_conjTranspose C hherm hidem hreal, hf]
  rcases p with ⟨b, p⟩
  cases b <;> simp only [hermitianColumn, Bool.false_eq_true, ite_false, ite_true]
  · rw [realPart_apply_coe, applySuper_real_smul, applySuper_add]
    simp only [Matrix.star_eq_conjTranspose, hf, hs]
  · rw [imaginaryPart_apply_coe, applySuper_smul, applySuper_real_smul, applySuper_sub]
    simp only [Matrix.star_eq_conjTranspose, hf, hs]

/-- Every unital, Hermitian, idempotent, realigned superoperator fixes all the
rank-one coordinate projectors of some orthonormal basis. -/
theorem exists_fixed_projection_basis (C : Matrix (n × n) (n × n) ℂ)
    (hherm : Cᴴ = C) (hidem : C * C = C) (hreal : IsRealigned C)
    (hunital : applySuper C 1 = 1) :
    ∃ b : OrthonormalBasis (Fin (Fintype.card n)) ℂ (EuclideanSpace ℂ n),
      ∀ j, applySuper C (projector (b j)) = projector (b j) := by
  classical
  let M := hermitianColumn C
  let T : Bool × (n × n) → End ℂ (EuclideanSpace ℂ n) :=
    fun p => Matrix.toEuclideanLin (M p)
  have hsym : ∀ p, (T p).IsSymmetric := fun p =>
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (hermitianColumn_isHermitian C p)
  have hcomm : Pairwise (Commute on T) := by
    intro p q _
    have h := super_fixedPoints_commute C hherm hidem hreal hunital (M p) (M q)
      (hermitianColumn_fixed C hherm hidem hreal p)
      (hermitianColumn_fixed C hherm hidem hreal q)
    exact h.map (Matrix.toLpLinAlgEquiv 2)
  obtain ⟨b₀, hb₀⟩ := exists_joint_projection_basis T hsym hcomm
  have hdim : finrank ℂ (EuclideanSpace ℂ n) = Fintype.card n :=
    finrank_euclideanSpace
  let b := b₀.reindex (finCongr hdim)
  refine ⟨b, ?_⟩
  intro j
  let Q := projector (b j)
  have hQM (p : Bool × (n × n)) : Commute Q (M p) := by
    apply (Matrix.toLpLinAlgEquiv 2).injective
    simp only [map_mul]
    change Matrix.toEuclideanLin Q * T p = T p * Matrix.toEuclideanLin Q
    change Matrix.toEuclideanLin (projector (b j)) * T p =
      T p * Matrix.toEuclideanLin (projector (b j))
    rw [toEuclideanLin_projector]
    have h := (hb₀ p ((finCongr hdim).symm j)).symm.eq
    simpa only [b, OrthonormalBasis.reindex_apply] using h
  have hQA (p : n × n) : Commute Q (superColumn C p) := by
    rw [← realPart_add_I_smul_imaginaryPart (superColumn C p)]
    exact (hQM (false, p)).add_right ((hQM (true, p)).smul_right Complex.I)
  rw [applySuper_eq_kraus_columns C hherm hidem hreal]
  change kraus (superColumn C) Q = Q
  have hunit : ∑ p, (superColumn C p)ᴴ * superColumn C p = 1 := by
    simpa only [applySuper_eq_kraus_columns C hherm hidem hreal, kraus, Matrix.mul_one]
      using hunital
  calc
    kraus (superColumn C) Q = ∑ p, (superColumn C p)ᴴ * (superColumn C p) * Q := by
      apply Finset.sum_congr rfl
      intro p _
      rw [Matrix.mul_assoc, (hQA p).eq, ← Matrix.mul_assoc]
    _ = (∑ p, (superColumn C p)ᴴ * superColumn C p) * Q := by rw [Matrix.sum_mul]
    _ = Q := by rw [hunit, Matrix.one_mul]

end MUB6.Weiner

end OAI
