import OAI.Combinatorics.SecondNeighborhood.GenericRankMatching
import OAI.Combinatorics.SecondNeighborhood.MatrixMapsPolynomial
import OAI.Combinatorics.SecondNeighborhood.Matching
import Mathlib.Data.Fintype.EquivFin

namespace OAI

namespace SeymourSecondNeighborhood.Pruning

open scoped Matrix

variable {X : Type*} [Fintype X] [DecidableEq X]

def matrixLSupport (r : X → X → Prop) (R C : Finset (X × X))
    (z : ↥(Z r R C)) (left : ↥R) : Prop :=
  z.val.2 = left.val.2 ∧ r left.val.1 z.val.1

def matrixNTransposeSupport (r : X → X → Prop) (R C : Finset (X × X))
    (z : ↥(Z r R C)) (right : ↥C) : Prop :=
  right.val.1 = z.val.1 ∧ r right.val.2 z.val.2

@[simp] theorem matrixLSupport_iff_leftCovers (r : X → X → Prop)
    (R C : Finset (X × X)) (z : ↥(Z r R C)) (left : ↥R) :
    matrixLSupport r R C z left ↔ LeftCovers r left.val z.val := by
  constructor
  · rintro ⟨hcoord, harrow⟩
    exact ⟨hcoord.symm, harrow⟩
  · rintro ⟨hcoord, harrow⟩
    exact ⟨hcoord.symm, harrow⟩

@[simp] theorem matrixNTransposeSupport_iff_rightCovers (r : X → X → Prop)
    (R C : Finset (X × X)) (z : ↥(Z r R C)) (right : ↥C) :
    matrixNTransposeSupport r R C z right ↔ RightCovers r right.val z.val :=
  Iff.rfl

noncomputable def matrixLMatchingMinor (r : X → X → Prop) (R C : Finset (X × X))
    (M : Finset (↥(Z r R C) × ↥R)) :
    Matrix ↥M ↥M (MvPolynomial (CoefficientVariables X) ℝ) :=
  (matrixLPolynomial r R C).submatrix (fun e : ↥M => e.val.1) (fun e => e.val.2)

noncomputable def matrixNTransposeMatchingMinor (r : X → X → Prop)
    (R C : Finset (X × X)) (M : Finset (↥(Z r R C) × ↥C)) :
    Matrix ↥M ↥M (MvPolynomial (CoefficientVariables X) ℝ) :=
  (matrixNPolynomial r R C)ᵀ.submatrix (fun e : ↥M => e.val.1) (fun e => e.val.2)

@[simp] theorem eval_matrixLMatchingMinor (r : X → X → Prop)
    (R C : Finset (X × X)) (M : Finset (↥(Z r R C) × ↥R))
    (v : CoefficientVariables X → ℝ) :
    evalPolynomialMatrix v (matrixLMatchingMinor r R C M) =
      (matrixL r R C (selectedA r v)).submatrix
        (fun e : ↥M => e.val.1) (fun e => e.val.2) := by
  rw [matrixLMatchingMinor, evalPolynomialMatrix_submatrix, eval_matrixLPolynomial]

@[simp] theorem eval_matrixNTransposeMatchingMinor (r : X → X → Prop)
    (R C : Finset (X × X)) (M : Finset (↥(Z r R C) × ↥C))
    (v : CoefficientVariables X → ℝ) :
    evalPolynomialMatrix v (matrixNTransposeMatchingMinor r R C M) =
      (matrixN r R C (selectedB r v))ᵀ.submatrix
        (fun e : ↥M => e.val.1) (fun e => e.val.2) := by
  rw [matrixNTransposeMatchingMinor, evalPolynomialMatrix_submatrix,
    eval_matrixNPolynomial_transpose]

theorem det_matrixLMatchingMinor_ne_zero (r : X → X → Prop)
    (R C : Finset (X × X)) (M : Finset (↥(Z r R C) × ↥R))
    (hM : Bipartite.IsMatching (matrixLSupport r R C) M) :
    (matrixLMatchingMinor r R C M).det ≠ 0 := by
  classical
  have hdiag : ∀ e : ↥M, matrixLSupport r R C e.val.1 e.val.2 :=
    fun e => hM.1 e.val e.property
  change (supportedVariableMatrix (R := ℝ)
    (fun e f : ↥M => matrixLSupport r R C e.val.1 f.val.2)
    (fun e f : ↥M =>
      (Sum.inl (f.val.2.val.1, e.val.1.val.1) : CoefficientVariables X))).det ≠ 0
  apply det_blockSupportedVariables_ne_zero _ _
    (fun e : ↥M => (Fintype.equivFin X) e.val.1.val.2)
  · exact hdiag
  · intro i j hij
    exact congrArg (Fintype.equivFin X) (hij.1.trans (hdiag j).1.symm)
  · intro i j k l hij hkl hblock hlabel
    have hsecond : i.val.1.val.2 = k.val.1.val.2 :=
      (Fintype.equivFin X).injective hblock
    have hp : (j.val.2.val.1, i.val.1.val.1) =
        (l.val.2.val.1, k.val.1.val.1) := Sum.inl.inj hlabel
    have hlabelFirst := congrArg (fun p : X × X => p.1) hp
    have hlabelSecond := congrArg (fun p : X × X => p.2) hp
    have hrow : i.val.1 = k.val.1 :=
      Subtype.ext (Prod.ext hlabelSecond hsecond)
    have hcolSecond := hij.1.symm.trans (hsecond.trans hkl.1)
    have hcol : j.val.2 = l.val.2 :=
      Subtype.ext (Prod.ext hlabelFirst hcolSecond)
    exact ⟨Subtype.ext (hM.2.1 i.property k.property hrow),
      Subtype.ext (hM.2.2 j.property l.property hcol)⟩

theorem det_matrixNTransposeMatchingMinor_ne_zero (r : X → X → Prop)
    (R C : Finset (X × X)) (M : Finset (↥(Z r R C) × ↥C))
    (hM : Bipartite.IsMatching (matrixNTransposeSupport r R C) M) :
    (matrixNTransposeMatchingMinor r R C M).det ≠ 0 := by
  classical
  have hdiag : ∀ e : ↥M, matrixNTransposeSupport r R C e.val.1 e.val.2 :=
    fun e => hM.1 e.val e.property
  change (supportedVariableMatrix (R := ℝ)
    (fun e f : ↥M => matrixNTransposeSupport r R C e.val.1 f.val.2)
    (fun e f : ↥M =>
      (Sum.inr (f.val.2.val.2, e.val.1.val.2) : CoefficientVariables X))).det ≠ 0
  apply det_blockSupportedVariables_ne_zero _ _
    (fun e : ↥M => (Fintype.equivFin X) e.val.1.val.1)
  · exact hdiag
  · intro i j hij
    exact congrArg (Fintype.equivFin X) (hij.1.symm.trans (hdiag j).1)
  · intro i j k l hij hkl hblock hlabel
    have hfirst : i.val.1.val.1 = k.val.1.val.1 :=
      (Fintype.equivFin X).injective hblock
    have hp : (j.val.2.val.2, i.val.1.val.2) =
        (l.val.2.val.2, k.val.1.val.2) := Sum.inr.inj hlabel
    have hlabelFirst := congrArg (fun p : X × X => p.1) hp
    have hlabelSecond := congrArg (fun p : X × X => p.2) hp
    have hrow : i.val.1 = k.val.1 :=
      Subtype.ext (Prod.ext hfirst hlabelSecond)
    have hcolFirst := hij.1.trans (hfirst.trans hkl.1.symm)
    have hcol : j.val.2 = l.val.2 :=
      Subtype.ext (Prod.ext hcolFirst hlabelFirst)
    exact ⟨Subtype.ext (hM.2.1 i.property k.property hrow),
      Subtype.ext (hM.2.2 j.property l.property hcol)⟩

end SeymourSecondNeighborhood.Pruning

end OAI
