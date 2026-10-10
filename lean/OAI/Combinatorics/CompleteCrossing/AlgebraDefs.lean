import OAI.Combinatorics.Crossing.NodeMoments
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Fin.VecNotation
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm

namespace OAI

/-! Polynomial spaces, interpolation weights, crossing tensors, and support evaluation. -/

section

/-! Polynomial spaces and crossing tensors for complete graphs.

These definitions contain no mathematical theorem assumptions. -/

open scoped BigOperators Classical

noncomputable section

namespace Paper170

abbrev Poly2 := MvPolynomial (Fin 2) ℝ
abbrev Poly4 := MvPolynomial (Fin 4) ℝ

def nodeWeight {ι : Type*} [Fintype ι] (node : ι → ℝ) (i : ι) : ℝ :=
  (Zarankiewicz.derivativeAtNode node i)⁻¹

def omittedNodePolynomial {ι : Type*} [Fintype ι] [DecidableEq ι]
    (node : ι → ℝ) (i : ι) : Polynomial ℝ :=
  ∏ j ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (node j))

def rectangle (a b : ℕ) : Submodule ℝ Poly2 :=
  MvPolynomial.degreesLE ℝ (Fin 2)
    (Multiset.replicate a 0 + Multiset.replicate b 1)

def box4 (d : ℕ) : Submodule ℝ Poly4 :=
  MvPolynomial.degreesLE ℝ (Fin 4) (d • (Finset.univ : Finset (Fin 4)).val)

def swapFirstPair : Poly4 →ₗ[ℝ] Poly4 :=
  (MvPolynomial.rename (Equiv.swap (0 : Fin 4) 1)).toLinearMap

def swapSecondPair : Poly4 →ₗ[ℝ] Poly4 :=
  (MvPolynomial.rename (Equiv.swap (2 : Fin 4) 3)).toLinearMap

def endpointSymmetricSpace (s : ℕ) : Submodule ℝ Poly4 :=
  box4 (s - 2) ⊓ LinearMap.ker (swapFirstPair - LinearMap.id) ⊓
    LinearMap.ker (swapSecondPair - LinearMap.id)

def evalTwo (u v : ℝ) : Poly2 →ₗ[ℝ] ℝ :=
  (MvPolynomial.aeval ![u, v]).toLinearMap

def evalFour (x u y v : ℝ) : Poly4 →ₗ[ℝ] ℝ :=
  (MvPolynomial.aeval ![x, u, y, v]).toLinearMap

/-- The manuscript's one-based L_s, translated to zero-based Fin indices. -/
def evenTriangle (s : ℕ) : Finset (Fin (2 * s) × Fin (2 * s)) :=
  Finset.univ.filter fun pq =>
    (pq.1.val < s ∧ pq.2 < pq.1) ∨ (s ≤ pq.1.val ∧ pq.1 < pq.2)

abbrev EvenTriangleCoord (s : ℕ) := ↥(evenTriangle s)

def triangleEvaluation (s a b : ℕ) (node : Fin (2 * s) → ℝ) :
    rectangle a b →ₗ[ℝ] (EvenTriangleCoord s → ℝ) :=
  LinearMap.pi fun pq =>
    (evalTwo (node pq.val.1) (node pq.val.2)).comp (rectangle a b).subtype

def halfOrder {ι : Type*} (order : LinearOrder ι) (p q : ι) : ℝ :=
  letI := order
  if p < q then 1 / 2 else if q < p then -(1 / 2) else 0

def weightedPairing {ι : Type*} [Fintype ι]
    (node : ι → ℝ) (K : ι → ι → ℝ) (A B : Poly2) : ℝ :=
  ∑ p, ∑ q, K p q * (node p - node q) /
    (Zarankiewicz.derivativeAtNode node p * Zarankiewicz.derivativeAtNode node q) *
    evalTwo (node p) (node q) A * evalTwo (node p) (node q) B

def orderPairing {ι : Type*} [Fintype ι]
    (node : ι → ℝ) (order : LinearOrder ι) (A B : Poly2) : ℝ :=
  weightedPairing node (halfOrder order) A B

abbrev CrossingTensor (n : ℕ) := Fin n → Fin n → Fin n → Fin n → ℝ

def chainBoundary {n : ℕ} (z : Fin n → Fin n → ℝ) (v : Fin n) : ℝ :=
  (∑ i, z i v) - ∑ p, z v p

def chainPairing {n : ℕ} (J : CrossingTensor n)
    (z z' : Fin n → Fin n → ℝ) : ℝ :=
  ∑ i, ∑ p, ∑ k, ∑ q, J i p k q * z i p * z' k q

def polynomialTest {n : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n)
    (H : Poly4) : ℝ :=
  ∑ i, ∑ p, ∑ k, ∑ q, J i p k q * nodeWeight node i * nodeWeight node p *
    nodeWeight node k * nodeWeight node q * evalFour (node i) (node p) (node k) (node q) H

/-- Canonical orientation within each edge; the two edges remain ordered. -/
def supportedPairs {n : ℕ} (J : CrossingTensor n) :
    Finset ((Fin n × Fin n) × (Fin n × Fin n)) :=
  Finset.univ.filter fun a =>
    a.1.1 < a.1.2 ∧ a.2.1 < a.2.2 ∧
    a.1.1 ≠ a.2.1 ∧ a.1.1 ≠ a.2.2 ∧
    a.1.2 ≠ a.2.1 ∧ a.1.2 ≠ a.2.2 ∧
    J a.1.1 a.1.2 a.2.1 a.2.2 ≠ 0

abbrev SupportCoord {n : ℕ} (J : CrossingTensor n) := ↥(supportedPairs J)

def supportEvaluation {n : ℕ} (s : ℕ) (node : Fin n → ℝ) (J : CrossingTensor n) :
    endpointSymmetricSpace s →ₗ[ℝ] (SupportCoord J → ℝ) :=
  LinearMap.pi fun a => (evalFour (node a.val.1.1) (node a.val.1.2)
    (node a.val.2.1) (node a.val.2.2)).comp (endpointSymmetricSpace s).subtype

/-- C=(x-y)(x-v)(u-y)(u-v), with coordinates x,u,y,v. -/
def collisionFactor : Poly4 :=
  (MvPolynomial.X 0 - MvPolynomial.X 2) *
  (MvPolynomial.X 0 - MvPolynomial.X 3) *
  (MvPolynomial.X 1 - MvPolynomial.X 2) *
  (MvPolynomial.X 1 - MvPolynomial.X 3)

/-- The complete six-difference product in the source's stated order. -/
def fullDifference : Poly4 :=
  (MvPolynomial.X 0 - MvPolynomial.X 1) *
  (MvPolynomial.X 2 - MvPolynomial.X 3) * collisionFactor

/-- Substitute x=y=t, leaving u,v as the two variables. -/
def vertexSpecialization (t : ℝ) : Poly4 →ₐ[ℝ] Poly2 :=
  MvPolynomial.aeval ![MvPolynomial.C t, MvPolynomial.X 0,
    MvPolynomial.C t, MvPolynomial.X 1]

/-- Substitute y=x, leaving x,u,v as three variables. -/
def diagonalSpecialization : Poly4 →ₐ[ℝ] MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.aeval ![MvPolynomial.X 0, MvPolynomial.X 1,
    MvPolynomial.X 0, MvPolynomial.X 2]

def supportDiagonal {n : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n)
    (a : SupportCoord J) : ℝ :=
  J a.val.1.1 a.val.1.2 a.val.2.1 a.val.2.2 *
    nodeWeight node a.val.1.1 * nodeWeight node a.val.1.2 *
    nodeWeight node a.val.2.1 * nodeWeight node a.val.2.2 *
    evalFour (node a.val.1.1) (node a.val.1.2) (node a.val.2.1) (node a.val.2.2)
      fullDifference

def supportBilinear {n : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n) :
    LinearMap.BilinForm ℝ (SupportCoord J → ℝ) :=
  Matrix.toBilin' (Matrix.diagonal (supportDiagonal node J))

def weightedChain {n : ℕ} (node : Fin n → ℝ) (a b : ℕ) (i p : Fin n) : ℝ :=
  nodeWeight node i * nodeWeight node p * node i ^ a * node p ^ b

def collisionFactors : Fin 4 → Poly4 :=
  ![MvPolynomial.X 0 - MvPolynomial.X 2,
    MvPolynomial.X 0 - MvPolynomial.X 3,
    MvPolynomial.X 1 - MvPolynomial.X 2,
    MvPolynomial.X 1 - MvPolynomial.X 3]

def liftUnivariate (i : Fin 4) (U : Polynomial ℝ) : Poly4 :=
  Polynomial.aeval (MvPolynomial.X i) U

def liftBivariate (i j : Fin 4) (B : Poly2) : Poly4 :=
  MvPolynomial.aeval ![MvPolynomial.X i, MvPolynomial.X j] B

def localTestPolynomial (P : Poly4) (U V : Polynomial ℝ) (B : Poly2) : Poly4 :=
  P * (MvPolynomial.X 1 - MvPolynomial.X 3) *
    (MvPolynomial.X 1 - MvPolynomial.X 2) * (MvPolynomial.X 3 - MvPolynomial.X 0) *
    liftUnivariate 0 U * liftUnivariate 2 V * liftBivariate 1 3 B

end Paper170

end
end

end OAI
