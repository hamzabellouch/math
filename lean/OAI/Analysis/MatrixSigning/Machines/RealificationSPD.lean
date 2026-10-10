import Mathlib
import OAI.Analysis.MatrixSigning.Machines.Realification

namespace OAI

section

namespace KS.W08

open Matrix
open scoped ComplexOrder BigOperators

def complexifyVector {n : Type*} (x : n ⊕ n → ℝ) : n → ℂ :=
  fun i => ⟨x (Sum.inl i), x (Sum.inr i)⟩

@[simp] theorem realifyVector_complexify {n : Type*} (x : n ⊕ n → ℝ) :
    realifyVector (complexifyVector x) = x := by
  funext i
  cases i <;> rfl

@[simp] theorem realifyVector_zero {n : Type*} : realifyVector (0 : n → ℂ) = 0 := by
  funext i
  cases i <;> rfl

theorem realify_conjTranspose {m n : Type*} (A : Matrix m n ℂ) :
    realify Aᴴ = (realify A)ᵀ := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [realify, Matrix.fromBlocks, Matrix.conjTranspose_apply, Matrix.transpose_apply]

theorem realify_isHermitian {n : Type*} (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    (realify A).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  have h := congrFun (congrFun (realify_conjTranspose A) j) i
  rw [hA] at h
  simpa using h

theorem realifyVector_dotProduct {n : Type*} [Fintype n] (x y : n → ℂ) :
    realifyVector x ⬝ᵥ realifyVector y = (star x ⬝ᵥ y).re := by
  simp [realifyVector, dotProduct, Fintype.sum_sum_type, Complex.mul_re,
    Finset.sum_add_distrib]

theorem realify_posDef {n : Type*} [Fintype n] (A : Matrix n n ℂ) (hA : A.PosDef) :
    (realify A).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (realify_isHermitian A hA.isHermitian)
  intro x hx
  have hc : complexifyVector x ≠ 0 := by
    intro hz
    apply hx
    have h := congrArg realifyVector hz
    simpa using h
  have hp := hA.re_dotProduct_pos hc
  have he : x ⬝ᵥ (realify A *ᵥ x) =
      (star (complexifyVector x) ⬝ᵥ (A *ᵥ complexifyVector x)).re := by
    rw [← realifyVector_dotProduct, realify_mulVec, realifyVector_complexify]
  simp only [star_trivial, he]
  exact hp

theorem rationalRealify_cast_posDef {n : Type*} [Fintype n]
    (A : Matrix n n KS.W01.RationalComplex)
    (hA : (embedComplexMatrix A).PosDef) :
    ((rationalRealify A).map (Rat.castHom ℝ)).PosDef := by
  have hc : (rationalRealify A).map (Rat.castHom ℝ) = realify (embedComplexMatrix A) :=
    rationalRealify_cast A
  rw [hc]
  exact realify_posDef _ hA

end KS.W08

end

end OAI
