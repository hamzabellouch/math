import OAI.Analysis.KadisonKastler.MatrixCorners
import OAI.Analysis.KadisonKastler.MatrixVonNeumann
import OAI.Analysis.KadisonKastler.RecoveryExpectation

namespace OAI

/-! # Concrete rows and coordinate contractions for scalar recovery

A recovery contraction supported on one outer matrix coordinate is exactly
an operator from the original algebra in that corner. Its row sandwich is
the recovery observable, including the two square-root dimension factors.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance recoveryRowsOrder (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance recoveryRowsStarOrder (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

/-- Coordinate evaluation and insertion are adjoints. -/
theorem coordinate_projection_adjoint (a : ι) :
    ((PiLp.proj 2 (fun _ : ι => H) a) : Generator.FiniteHilbert ι H →L[ℂ] H).adjoint =
      Generator.tupleSingle (H := H) a := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp [PiLp.inner_apply, Generator.tupleSingle_apply, Pi.single_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hba
    simp [hba]
  · simp

/-- The represented single-entry matrix is the coordinate insertion/evaluation
sandwich of its original-algebra entry. -/
theorem matrixOperatorHom_matrixCorner (M : VonNeumannAlgebra H) (a : ι)
    (x : Algebra M) :
    matrixOperatorHom M (matrixCorner a x) =
      (Generator.tupleSingle a).comp (x.val.comp (PiLp.proj 2 (fun _ : ι => H) a)) := by
  ext ξ i
  by_cases hi : i = a
  · subst i
    simp [matrixOperatorHom_apply, hilbertMatrix_apply, matrixCorner,
      Matrix.single_apply, Generator.tupleSingle_apply, apply_ite]
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hba
      simp [Ne.symm hba]
    · simp
  · simp [matrixOperatorHom_apply, hilbertMatrix_apply, matrixCorner,
      Generator.tupleSingle_apply, hi, Ne.symm hi]

/-- Extract the original-algebra entry of an operator in the represented matrix
algebra. Membership is part of the returned subtype. -/
def coordinateCornerEntry (M : VonNeumannAlgebra H) (a : ι)
    (c : Algebra (matrixVonNeumann (ι := ι) M)) : Algebra M :=
  ((matrixAlgebraEquiv (ι := ι) M).symm c) a a

theorem norm_coordinateCornerEntry_le (M : VonNeumannAlgebra H) (a : ι)
    (c : Algebra (matrixVonNeumann (ι := ι) M)) :
    ‖coordinateCornerEntry M a c‖ ≤ ‖c‖ := by
  calc
    ‖coordinateCornerEntry M a c‖ ≤ ‖(matrixAlgebraEquiv (ι := ι) M).symm c‖ := by
      change ‖((matrixAlgebraEquiv (ι := ι) M).symm c) a a‖ ≤ _
      exact CStarMatrix.norm_entry_le_norm
        (M := (matrixAlgebraEquiv (ι := ι) M).symm c) (i := a) (j := a)
    _ = ‖c‖ := by
      rw [← norm_matrixOperatorHom M, matrixAlgebraEquiv_symm_operator]
      rfl

/-- Support by a coordinate projection gives exact corner reconstruction. -/
theorem coordinateCornerEntry_reconstruct (M : VonNeumannAlgebra H) (a : ι)
    (c : Algebra (matrixVonNeumann (ι := ι) M))
    (hl : matrixDiagonalProjection M a * c = c)
    (hr : c * matrixDiagonalProjection M a = c) :
    c.val = (Generator.tupleSingle a).comp
      ((coordinateCornerEntry M a c).val.comp (PiLp.proj 2 (fun _ : ι => H) a)) := by
  let C := (matrixAlgebraEquiv (ι := ι) M).symm c
  have hleft : matrixCorner a 1 * C = C := by
    apply (matrixAlgebraEquiv (ι := ι) M).injective
    change (matrixAlgebraEquiv (ι := ι) M) (matrixCorner a 1 * C) =
      (matrixAlgebraEquiv (ι := ι) M) C
    rw [map_mul]
    change (matrixAlgebraEquiv (ι := ι) M) (matrixCorner a 1) *
      (matrixAlgebraEquiv (ι := ι) M) ((matrixAlgebraEquiv (ι := ι) M).symm c) =
      (matrixAlgebraEquiv (ι := ι) M) ((matrixAlgebraEquiv (ι := ι) M).symm c)
    rw [StarAlgEquiv.apply_symm_apply]
    exact hl
  have hright : C * matrixCorner a 1 = C := by
    apply (matrixAlgebraEquiv (ι := ι) M).injective
    change (matrixAlgebraEquiv (ι := ι) M) (C * matrixCorner a 1) =
      (matrixAlgebraEquiv (ι := ι) M) C
    rw [map_mul]
    change (matrixAlgebraEquiv (ι := ι) M) ((matrixAlgebraEquiv (ι := ι) M).symm c) *
      (matrixAlgebraEquiv (ι := ι) M) (matrixCorner a 1) =
      (matrixAlgebraEquiv (ι := ι) M) ((matrixAlgebraEquiv (ι := ι) M).symm c)
    rw [StarAlgEquiv.apply_symm_apply]
    exact hr
  have hC := matrixCorner_reconstruct a C hleft hright
  calc
    c.val = matrixOperatorHom M C := (matrixAlgebraEquiv_symm_operator M c).symm
    _ = matrixOperatorHom M (matrixCorner a (C a a)) := congrArg _ hC
    _ = _ := matrixOperatorHom_matrixCorner M a _

variable {n : ℕ}

/-- The original-factor contraction obtained from the recovery operator. -/
def recoveryCornerContraction (M : VonNeumannAlgebra H) (a : Fin n)
    (f : Algebra (matrixVonNeumann (ι := Fin n) M)) : Algebra M :=
  coordinateCornerEntry M a (recoveryContraction n (matrixDiagonalProjection M a) f)

theorem recoveryCornerContraction_norm_le (M : VonNeumannAlgebra H)
    (hn : 0 < n) (a : Fin n) (f : Algebra (matrixVonNeumann (ι := Fin n) M)) :
    ‖recoveryCornerContraction M a f‖ ≤ 1 :=
  (norm_coordinateCornerEntry_le M a _).trans (recoveryContraction_norm_le hn _ _)

theorem recoveryCornerContraction_reconstruct (M : VonNeumannAlgebra H)
    (hn : 0 < n) (a : Fin n) (f : Algebra (matrixVonNeumann (ι := Fin n) M)) :
    (recoveryContraction n (matrixDiagonalProjection M a) f).val =
      (Generator.tupleSingle a).comp
        ((recoveryCornerContraction M a f).val.comp
          (PiLp.proj 2 (fun _ : Fin n => H) a)) := by
  obtain ⟨hl, hr⟩ := recoveryContraction_support hn (matrixDiagonalProjection M a) f
    (matrixDiagonalProjection_isStarProjection M a)
  exact coordinateCornerEntry_reconstruct M a _ hl hr

/-- The actual forward row of the normalized polynomial. -/
def recoveryForwardRow (M : VonNeumannAlgebra H) (N : ℕ) (a : Fin n)
    (v : unitary (Algebra (matrixVonNeumann (ι := Fin n) M))) :
    Generator.FiniteHilbert (Fin n) H →L[ℂ] H :=
  (Real.sqrt (n : ℝ) : ℂ) •
    (PiLp.proj 2 (fun _ : Fin n => H) a).comp (unitaryHaarPolynomial N v).val

/-- The backward row is formed from the adjoint polynomial. -/
def recoveryBackwardRow (M : VonNeumannAlgebra H) (N : ℕ) (a : Fin n)
    (v : unitary (Algebra (matrixVonNeumann (ι := Fin n) M))) :
    Generator.FiniteHilbert (Fin n) H →L[ℂ] H :=
  (Real.sqrt (n : ℝ) : ℂ) •
    (PiLp.proj 2 (fun _ : Fin n => H) a).comp (star (unitaryHaarPolynomial N v)).val

theorem recoveryBackwardRow_adjoint (M : VonNeumannAlgebra H) (N : ℕ) (a : Fin n)
    (v : unitary (Algebra (matrixVonNeumann (ι := Fin n) M))) :
    (recoveryBackwardRow M N a v).adjoint =
      (Real.sqrt (n : ℝ) : ℂ) •
        (unitaryHaarPolynomial N v).val.comp (Generator.tupleSingle a) := by
  have hstar : ((star (unitaryHaarPolynomial N v)).val).adjoint =
      (unitaryHaarPolynomial N v).val := by
    change ((unitaryHaarPolynomial N v).val.adjoint).adjoint = _
    exact ContinuousLinearMap.adjoint_adjoint _
  rw [recoveryBackwardRow, map_smulₛₗ, ContinuousLinearMap.adjoint_comp,
    coordinate_projection_adjoint, hstar]
  exact congrArg
    (fun z : ℂ => z • (unitaryHaarPolynomial N v).val.comp (Generator.tupleSingle a))
    (Complex.conj_ofReal (Real.sqrt (n : ℝ)))

/-- The corner contraction and the two normalized rows give precisely the
observable whose weak limit is computed by the free-Haar argument. -/
theorem recoveryRows_product (M : VonNeumannAlgebra H) (hn : 0 < n)
    (N : ℕ) (a : Fin n)
    (v : unitary (Algebra (matrixVonNeumann (ι := Fin n) M))) :
    (recoveryBackwardRow M N a v).adjoint.comp
      ((recoveryCornerContraction M a (unitaryHaarPolynomial N v)).val.comp
        (recoveryForwardRow M N a v)) =
      (recoveryObservable n N (matrixDiagonalProjection M a) v).val := by
  rw [recoveryBackwardRow_adjoint]
  have hrec := recoveryCornerContraction_reconstruct M hn a (unitaryHaarPolynomial N v)
  have hsqrt : (Real.sqrt (n : ℝ) : ℂ) * (Real.sqrt (n : ℝ) : ℂ) = (n : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg n)]
    simp
  apply ContinuousLinearMap.ext
  intro ξ
  change (Real.sqrt (n : ℝ) : ℂ) •
    (unitaryHaarPolynomial N v).val
      (Generator.tupleSingle a
        ((recoveryCornerContraction M a (unitaryHaarPolynomial N v)).val
          ((recoveryForwardRow M N a v) ξ))) = _
  simp only [recoveryForwardRow, smul_apply,
    ContinuousLinearMap.comp_apply, map_smul, smul_smul, hsqrt]
  change (n : ℂ) •
    (unitaryHaarPolynomial N v).val
      ((Generator.tupleSingle a).comp
        ((recoveryCornerContraction M a (unitaryHaarPolynomial N v)).val.comp
          (PiLp.proj 2 (fun _ : Fin n => H) a))
            ((unitaryHaarPolynomial N v).val ξ)) = _
  rw [← hrec]
  rfl

end

end KadisonKastler

end OAI
