import Mathlib
import OAI.Analysis.Commutator.MatrixDiffuseTransfer

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

namespace Kadison.OperatorAmplification

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type) [Fintype ι] (i₀ : ι) (M : VonNeumannAlgebra H)

local instance amplifiedTowerStageDecidableEq : DecidableEq ι := Classical.decEq ι

omit [CompleteSpace H] [Fintype ι] in
lemma matrixUnit_mul (i j k l : ι) : matrixUnit (H:=H) ι i j*matrixUnit ι k l=
    if j=k then matrixUnit ι i l else 0 := by
  ext x a
  by_cases h : j=k
  · subst k
    simp [mul_apply_eq_comp]
  · simp [mul_apply_eq_comp,single_apply,h]

lemma matrixUnit_star (i j : ι) : star (matrixUnit (H:=H) ι i j)=matrixUnit ι j i := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp only [matrixUnit_apply,PiLp.inner_apply,single_apply]
  have hl : (∑ k : ι,inner ℂ (if k=j then x i else 0) (y k))=inner ℂ (x i) (y j) := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      simp [hk]
    · simp
  have hr : (∑ k : ι,inner ℂ (x k) (if k=i then y j else 0))=inner ℂ (x i) (y j) := by
    simp [apply_ite]
  exact hl.trans hr.symm

omit [CompleteSpace H] in
lemma sum_matrixUnit : (∑ i : ι,matrixUnit (H:=H) ι i i)=1 := by
  ext x a
  simp [matrixUnit_apply,single_apply]

def scalarMatrixHom : Matrix ι ι ℂ →⋆ₐ[ℂ] matrixVonNeumann ι i₀ M :=
  MatrixUnits.representation (fun i j => ⟨matrixUnit ι i j,matrixUnit_mem ι i₀ M i j⟩)
    (by
      intro i j k l
      apply Subtype.ext
      change matrixUnit ι i j*matrixUnit ι k l=_
      rw [matrixUnit_mul]
      split_ifs <;> rfl)
    (by intro i j; apply Subtype.ext; exact matrixUnit_star ι i j)
    (by
      apply Subtype.ext
      change (matrixVonNeumann ι i₀ M).toStarSubalgebra.subtype
        (∑ i : ι,⟨matrixUnit ι i i,matrixUnit_mem ι i₀ M i i⟩)=1
      rw [map_sum]
      exact sum_matrixUnit (H:=H) ι)

lemma scalarMatrixHom_single (i j : ι) :
    (scalarMatrixHom ι i₀ M (Matrix.single i j 1):SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)=matrixUnit ι i j := by
  simp [scalarMatrixHom,MatrixUnits.representation,Matrix.single_apply,ite_and]

lemma scalarMatrixHom_coe (x : Matrix ι ι ℂ) :
    (scalarMatrixHom ι i₀ M x:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)=
      ∑ i,∑ j,x i j • matrixUnit ι i j := by
  change (matrixVonNeumann ι i₀ M).toStarSubalgebra.subtype
    (∑ i,∑ j,x i j • ⟨matrixUnit ι i j,matrixUnit_mem ι i₀ M i j⟩)=_
  simp only [map_sum,map_smul]
  rfl

lemma scalar_diagonal_commute (x : Matrix ι ι ℂ) (a : M) :
    Commute (scalarMatrixHom ι i₀ M x) (diagonalHom ι i₀ M a) := by
  change _*_=_*_
  apply Subtype.ext
  change (scalarMatrixHom ι i₀ M x:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)*
    (diagonalHom ι i₀ M a:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)=
    (diagonalHom ι i₀ M a:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)*
    (scalarMatrixHom ι i₀ M x:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)
  rw [scalarMatrixHom_coe,coe_diagonalHom]
  simp only [Finset.sum_mul,Finset.mul_sum,smul_mul_assoc,mul_smul_comm,matrixUnit_commutes]

variable (E : MatrixTower.Stage M)

def amplifiedStage : MatrixTower.Stage (matrixVonNeumann ι i₀ M) where
  I := ι×E.I
  finite := inferInstance
  dec := inferInstance
  nonempty := ⟨(i₀,Classical.choice inferInstance)⟩
  hom := MatrixTensor.representation (scalarMatrixHom ι i₀ M) ((diagonalHom ι i₀ M).comp E.hom)
    (fun x y => scalar_diagonal_commute ι i₀ M x (E.hom y))

lemma amplifiedStage_scalar (a : Matrix ι ι ℂ) :
    scalarMatrixHom ι i₀ M a∈(amplifiedStage ι i₀ M E).hom.range := by
  have hh := MatrixTensor.left_mem (A := matrixVonNeumann ι i₀ M)
    (I := ι) (J := E.I) (scalarMatrixHom ι i₀ M) ((diagonalHom ι i₀ M).comp E.hom)
    (fun x y => scalar_diagonal_commute ι i₀ M x (E.hom y)) a
  obtain ⟨b,hb⟩ := hh
  exact ⟨b,hb⟩

lemma amplifiedStage_diagonal (a : Matrix E.I E.I ℂ) :
    diagonalHom ι i₀ M (E.hom a)∈(amplifiedStage ι i₀ M E).hom.range := by
  have hh := MatrixTensor.right_mem (A := matrixVonNeumann ι i₀ M)
    (I := ι) (J := E.I) (scalarMatrixHom ι i₀ M) ((diagonalHom ι i₀ M).comp E.hom)
    (fun x y => scalar_diagonal_commute ι i₀ M x (E.hom y)) a
  obtain ⟨b,hb⟩ := hh
  exact ⟨b,hb⟩

end Kadison.OperatorAmplification

end

end
end

end OAI
