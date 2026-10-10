import OAI.AlgebraicGeometry.StableCoordinate.GradedRelation
import OAI.AlgebraicGeometry.StableCoordinate.HomogeneousQuotient
import Mathlib.Tactic.Ring

namespace OAI

/-!
# The actual integer grading of the degeneration ring

The quotient `G = k[p,s,u,F,J]/(Hstar)` carries the grading with weights
`(-1,0,0,1,1)`.  This file constructs that grading, rather than assuming it,
and records the degree-zero quadric coordinates used in the Laurent picture.
It does not identify `G` with the associated graded ring of `A`.
-/

noncomputable section

namespace StableCoordinate.Obstruction

open MvPolynomial

variable (k : Type*) [CommRing k]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-- The degree-`n` submodule in the actual principal quotient `G`. -/
def gPiece (n : ℤ) : Submodule k (G k) :=
  HomogeneousQuotient.piece (weightedHomogeneousSubmodule k presentationWeight) (idealG k) n

/-- Quotient homogeneity gives a genuine integer-graded algebra structure. -/
instance gGradedAlgebra : GradedAlgebra (gPiece k) :=
  HomogeneousQuotient.gradedAlgebra (weightedHomogeneousSubmodule k presentationWeight)
    (idealG k) (idealG_homogeneous k)

/-- Images of weighted-homogeneous polynomials lie in the specified quotient piece. -/
theorem mk_mem_gPiece {n : ℤ} {q : P k 5}
    (hq : q.IsWeightedHomogeneous presentationWeight n) :
    Ideal.Quotient.mk (idealG k) q ∈ gPiece k n :=
  HomogeneousQuotient.mk_mem_piece _ _ hq

/-- Each presentation generator retains its assigned (possibly negative) weight. -/
theorem gX_mem_piece (i : Fin 5) : gX k i ∈ gPiece k (presentationWeight i) :=
  mk_mem_gPiece k (isWeightedHomogeneous_X k presentationWeight i)

/-- The weight-zero invariant `x` in the degeneration ring. -/
def xG : G k := gX k 1 ^ 2 - gX k 2 ^ 2 + gX k 0 * gX k 3

/-- The weight-zero invariant `y` in the degeneration ring. -/
def yG : G k := gX k 1 + xG k * (xG k + gX k 2 ^ 2)

/-- The weight-zero invariant `z` in the degeneration ring. -/
def zG : G k := gX k 1 * xG k + gX k 0 * gX k 4

@[simp] theorem mk_xP : Ideal.Quotient.mk (idealG k) (xP k) = xG k := by
  simp [xP, xG, gX]

/-- The distinguished determinant invariant is homogeneous of degree zero. -/
theorem xG_mem_piece : xG k ∈ gPiece k 0 := by
  simpa using mk_mem_gPiece k (xP_homogeneous k)

/-- Products of two degree-zero elements again have degree zero. -/
theorem mul_mem_gPiece_zero {a b : G k} (ha : a ∈ gPiece k 0) (hb : b ∈ gPiece k 0) :
    a * b ∈ gPiece k 0 := by
  simpa using SetLike.GradedMul.mul_mem ha hb

/-- The second quadric coordinate has degree zero. -/
theorem yG_mem_piece : yG k ∈ gPiece k 0 := by
  have hs : gX k 1 ∈ gPiece k 0 := by simpa [presentationWeight] using gX_mem_piece k 1
  have hu : gX k 2 ∈ gPiece k 0 := by simpa [presentationWeight] using gX_mem_piece k 2
  have hu2 : gX k 2 ^ 2 ∈ gPiece k 0 := by
    simpa [pow_two] using mul_mem_gPiece_zero k hu hu
  exact (gPiece k 0).add_mem hs
    (mul_mem_gPiece_zero k (xG_mem_piece k) ((gPiece k 0).add_mem (xG_mem_piece k) hu2))

/-- The third quadric coordinate has degree zero. -/
theorem zG_mem_piece : zG k ∈ gPiece k 0 := by
  have hs : gX k 1 ∈ gPiece k 0 := by simpa [presentationWeight] using gX_mem_piece k 1
  have hpJ : gX k 0 * gX k 4 ∈ gPiece k 0 := by
    simpa [presentationWeight] using
      SetLike.GradedMul.mul_mem (gX_mem_piece k 0) (gX_mem_piece k 4)
  exact (gPiece k 0).add_mem (mul_mem_gPiece_zero k hs (xG_mem_piece k)) hpJ

/-- The variable `u` on the quadric is the original weight-zero generator. -/
theorem uG_mem_piece : gX k 2 ∈ gPiece k 0 := by
  simpa [presentationWeight] using gX_mem_piece k 2

/-- The defining equation of `G` in its named generators. -/
theorem g_relation :
    xG k ^ 2 * gX k 3 - (1 + 2 * gX k 1 * xG k) * gX k 4 -
      gX k 0 * gX k 4 ^ 2 = 0 := by
  simpa [Hstar, xP, xG, gX, map_ofNat] using mk_Hstar k

/-- The quadric equation follows from the actual defining relation of `G`. -/
theorem g_quadric_relation : xG k * yG k - zG k * (zG k + 1) = 0 := by
  calc
    xG k * yG k - zG k * (zG k + 1) =
      gX k 0 * (xG k ^ 2 * gX k 3 -
        (1 + 2 * gX k 1 * xG k) * gX k 4 - gX k 0 * gX k 4 ^ 2) := by
      unfold yG zG xG
      ring
    _ = 0 := by rw [g_relation k, mul_zero]


/-- Polynomial map implementing the quadric coordinates in `G`. -/
def baseToDegenerationPre : P k 4 →ₐ[k] G k :=
  MvPolynomial.aeval ![xG k, yG k, zG k, gX k 2]

/-- The quadric relation vanishes under the polynomial substitution. -/
theorem baseToDegenerationPre_relation :
    baseToDegenerationPre k (quadricRelation k) = 0 := by
  simpa [baseToDegenerationPre, quadricRelation] using g_quadric_relation k

/-- The canonical algebra homomorphism from the quadric ring into `G`. -/
def baseToDegeneration : B k →ₐ[k] G k :=
  Ideal.Quotient.liftₐ (idealB k) (baseToDegenerationPre k) (by
    intro q hq
    change q ∈ Ideal.span ({quadricRelation k} : Set (P k 4)) at hq
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hq
    simp [map_mul, baseToDegenerationPre_relation])

@[simp] theorem baseToDegeneration_mk (q : P k 4) :
    baseToDegeneration k (Ideal.Quotient.mk (idealB k) q) =
      baseToDegenerationPre k q := rfl

@[simp] theorem baseToDegeneration_bX (i : Fin 4) :
    baseToDegeneration k (bX k i) = ![xG k, yG k, zG k, gX k 2] i := by
  simp [bX, baseToDegeneration_mk, baseToDegenerationPre]

/-- All four polynomial substitution values lie in degree zero. -/
theorem baseToDegenerationPre_X_mem_piece (i : Fin 4) :
    baseToDegenerationPre k (X i) ∈ gPiece k 0 := by
  simp only [baseToDegenerationPre, aeval_X]
  fin_cases i
  · exact xG_mem_piece k
  · exact yG_mem_piece k
  · exact zG_mem_piece k
  · exact uG_mem_piece k

/-- The complete quadric coordinate ring lands in weight zero. -/
theorem baseToDegeneration_mem_piece (q : B k) :
    baseToDegeneration k q ∈ gPiece k 0 := by
  refine Quotient.inductionOn' q ?_
  intro p
  change baseToDegenerationPre k p ∈ gPiece k 0
  induction p using MvPolynomial.induction_on with
  | C r =>
      simp only [baseToDegenerationPre, aeval_C]
      rw [← (Ideal.Quotient.mkₐ k (idealG k)).commutes r]
      exact mk_mem_gPiece k (isWeightedHomogeneous_C presentationWeight r)
  | add p q hp hq =>
      rw [map_add]
      exact (gPiece k 0).add_mem hp hq
  | mul_X p i hp =>
      rw [map_mul]
      exact mul_mem_gPiece_zero k hp (baseToDegenerationPre_X_mem_piece k i)


@[simp] theorem baseToDegeneration_sB :
    baseToDegeneration k (sB k) = gX k 1 := by
  simp only [sB, map_sub, map_mul, map_add, map_pow, baseToDegeneration_bX]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val,
    yG]
  ring

@[simp] theorem baseToDegeneration_f0 :
    baseToDegeneration k (f0 k) = gX k 0 * gX k 3 := by
  simp only [f0, map_sub, map_add, map_pow, baseToDegeneration_bX, baseToDegeneration_sB]
  simp only [Matrix.cons_val_zero, Matrix.cons_val, xG]
  ring

@[simp] theorem baseToDegeneration_g0 :
    baseToDegeneration k (g0 k) = gX k 0 * gX k 4 := by
  simp only [g0, map_sub, map_mul, baseToDegeneration_bX, baseToDegeneration_sB]
  simp only [Matrix.cons_val_zero, Matrix.cons_val, zG]
  ring

end StableCoordinate.Obstruction

end

end OAI
