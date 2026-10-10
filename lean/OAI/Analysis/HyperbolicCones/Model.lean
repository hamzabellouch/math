import Mathlib

namespace OAI

/-! The Choi–Lam form, determinant polynomial, root-defined cone, and quadratic deformation. -/

noncomputable section

open scoped Matrix.Norms.L2Operator

universe u

namespace Paper256

abbrev Mat (n : ℕ) (R : Type u) := Matrix (Fin n) (Fin n) R

abbrev Sym (n : ℕ) := selfAdjoint (Mat n ℝ)

instance instFiniteDimensionalSym (n : ℕ) : FiniteDimensional ℝ (Sym n) :=
  FiniteDimensional.finiteDimensional_submodule (selfAdjoint.submodule ℝ (Mat n ℝ))

abbrev Ambient := (Sym 4 × Sym 4) × (Fin 3 → ℝ)

abbrev SymIndex := {ij : Fin 4 × Fin 4 // ij.1 ≤ ij.2}

abbrev Coord := (SymIndex ⊕ SymIndex) ⊕ Fin 3

def qMatrix {R : Type u} [CommRing R] (y : Fin 3 → R) : Mat 3 R :=
  fun i j => if i = j then y i ^ 2 + y (i + 1) ^ 2 else -(y i * y j)

def phi {R : Type u} [CommRing R] (y : Fin 3 → R) (X : Mat 4 R) : Mat 4 R :=
  fun i j => Fin.cases
    (Fin.cases
      (Matrix.trace (qMatrix y * X.submatrix Fin.succ Fin.succ))
      (fun j => -(∑ k, X 0 k.succ * qMatrix y k j)) j)
    (fun i => Fin.cases
      (-(∑ k, qMatrix y i k * X k.succ 0))
      (fun j => X 0 0 * qMatrix y i j) j) i

def matrixValue {R : Type u} [CommRing R]
    (X Z : Mat 4 R) (y : Fin 3 → R) : R :=
  Matrix.det ((Matrix.det X) • Z - phi y (Matrix.adjugate X))

def symmetricCoordinates {R : Type u} (v : SymIndex → R) : Mat 4 R :=
  fun i j => if h : i ≤ j then v ⟨(i, j), h⟩
    else v ⟨(j, i), le_of_lt (lt_of_not_ge h)⟩

def polynomial : MvPolynomial Coord ℝ :=
  matrixValue
    (symmetricCoordinates fun ij => MvPolynomial.X (Sum.inl (Sum.inl ij)))
    (symmetricCoordinates fun ij => MvPolynomial.X (Sum.inl (Sum.inr ij)))
    (fun i => MvPolynomial.X (Sum.inr i))

def coordinates (x : Ambient) : Coord → ℝ :=
  Sum.elim (Sum.elim
    (fun ij => (x.1.1 : Mat 4 ℝ) ij.val.1 ij.val.2)
    (fun ij => (x.1.2 : Mat 4 ℝ) ij.val.1 ij.val.2)) x.2

def basePoint : Ambient := ((1, 1), 0)

def linePolynomial (x : Ambient) : Polynomial ℝ :=
  MvPolynomial.eval₂ Polynomial.C
    (fun i => Polynomial.C (coordinates basePoint i) * Polynomial.X -
      Polynomial.C (coordinates x i)) polynomial

def cone : Set Ambient :=
  {x | ∀ t : ℂ, (linePolynomial x).aeval t = 0 → t.im = 0 ∧ 0 ≤ t.re}

def choiLam {R : Type u} [CommRing R] (z y : Fin 3 → R) : R :=
  (∑ i, z i ^ 2 * y i ^ 2) -
    2 * (z 0 * y 0 * z 1 * y 1 + z 0 * y 0 * z 2 * y 2 +
      z 1 * y 1 * z 2 * y 2) +
    (∑ i, z i ^ 2 * y (i + 1) ^ 2)

def zMatrix {R : Type u} [CommRing R] (z : Fin 3 → R) : Mat 3 R :=
  fun i j => if i = j then z i ^ 2 + z (i + 2) ^ 2 else -(z i * z j)

def intervalPolynomial (a b : ℝ) : Polynomial ℝ :=
  (1 - Polynomial.C a⁻¹ * Polynomial.X) * (1 + Polynomial.C b⁻¹ * Polynomial.X)

def timeScale (η t : ℝ) : ℝ := 1 + η * Real.sin (Real.pi * t) ^ 2

def deformedPolynomial (a b η t : ℝ) : Polynomial ℝ :=
  (intervalPolynomial a b).comp (Polynomial.C (timeScale η t) * Polynomial.X)

def rigidlyConvexSet (p : Polynomial ℝ) : Set ℝ :=
  closure (connectedComponentIn {x : ℝ | p.eval x ≠ 0} 0)

open scoped BigOperators RealInnerProductSpace
open Set Filter Matrix

abbrev Vec (n : ℕ) := EuclideanSpace ℝ (Fin n)

def outer {n : ℕ} (v : Vec n) : Mat n ℝ := fun i j => v i * v j

def outerSym {n : ℕ} (v : Vec n) : Sym n :=
  ⟨outer v, by
    change (outer v)ᴴ = outer v
    ext i j
    simp [outer, Matrix.conjTranspose_apply, mul_comm]⟩

def operatorNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ‖A.toEuclideanLin.toContinuousLinearMap‖

def kernelProjection {n : ℕ} (A : Mat n ℝ) : Mat n ℝ :=
  Matrix.toEuclideanLin.symm (A.toEuclideanLin.ker.starProjection.toLinearMap)

def inverseSquareRoot {n : ℕ} (A : Sym n) : Mat n ℝ :=
  let hA : (A : Mat n ℝ).IsHermitian := A.property
  let U : Mat n ℝ := hA.eigenvectorUnitary
  U * Matrix.diagonal (fun i => (Real.sqrt (hA.eigenvalues i))⁻¹) * Uᴴ

/-- The vector v₀u′−u₀v′ in the rank-one and operator-norm identities. -/
def wedgeCoordinates (v u : Vec 4) : Fin 3 → ℝ :=
  fun i => v 0 * u i.succ - u 0 * v i.succ

def tangentCurve (v h : Vec 4) (s : ℝ) : Vec 4 :=
  (Real.sqrt (1 + s ^ 2 * ‖h‖ ^ 2))⁻¹ • (v + s • h)

def tangentSpace (v : Vec 4) : Submodule ℝ (Vec 4) := (innerSL ℝ v).ker

/-- Positive unital diagonal blocks with an exact Schur-complement equivalence. -/
structure NormalizedPencil where
  a : ℕ
  c : ℕ
  a_pos : 0 < a
  c_pos : 0 < c
  D : Sym 4 →ₗ[ℝ] Sym a
  E : Sym 4 →ₗ[ℝ] Sym c
  B : (Fin 3 → ℝ) →ₗ[ℝ] Matrix (Fin a) (Fin c) ℝ
  D_positive : ∀ X : Sym 4, (X : Mat 4 ℝ).PosSemidef → (D X : Mat a ℝ).PosSemidef
  E_positive : ∀ X : Sym 4, (X : Mat 4 ℝ).PosSemidef → (E X : Mat c ℝ).PosSemidef
  D_unital : D 1 = 1
  E_unital : E 1 = 1
  schur_equivalence : ∀ (X Z : Sym 4) (y : Fin 3 → ℝ) (_hX : (X : Mat 4 ℝ).PosDef),
    ((Z : Mat 4 ℝ) - phi y (X : Mat 4 ℝ)⁻¹).PosSemidef ↔
      ((E Z : Mat c ℝ) - (B y)ᵀ * (D X : Mat a ℝ)⁻¹ * B y).PosSemidef

def NormalizedPencil.leftProjection (P : NormalizedPencil) (v : Vec 4) : Mat P.a ℝ :=
  kernelProjection (P.D (1 - outerSym v) : Mat P.a ℝ)

def NormalizedPencil.rightProjection (P : NormalizedPencil) (v : Vec 4) : Mat P.c ℝ :=
  kernelProjection (P.E (1 - outerSym v) : Mat P.c ℝ)

def deformedPencil (a b η t x : ℝ) : Mat 2 ℝ :=
  Matrix.diagonal ![1 - timeScale η t * x / a, 1 + timeScale η t * x / b]

def deformedCoefficients (a b η t : ℝ) : Fin 3 → ℝ :=
  fun i => (deformedPolynomial a b η t).coeff i.val


end Paper256

end

end OAI
