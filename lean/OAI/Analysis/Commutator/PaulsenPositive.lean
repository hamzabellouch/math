import Mathlib
import OAI.Analysis.Commutator.FaithfulPositive
import OAI.Analysis.Commutator.MatrixScalar
import OAI.Analysis.Commutator.PaulsenSystem
import OAI.Analysis.Commutator.OperatorSystem
import OAI.Analysis.Commutator.SchurTransfer

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators ComplexOrder

namespace Kadison.Paulsen

open CStarBlock MatrixScalar OperatorSystem

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

local instance : DecidableEq (Fin 2) := Classical.decEq (Fin 2)

def IsCompletelyContractive (f : A →ₗ[ℂ] B) : Prop :=
  ∀ (ι : Type) [Fintype ι] (X : CStarMatrix ι ι A),‖CStarMatrix.mapₗ f X‖≤‖X‖

namespace MatrixTest

variable [Nontrivial A] {ι : Type} [Fintype ι]

local instance : DecidableEq ι := Classical.decEq ι

def leftDiagonal (X : matrices (system A) ι) : CStarMatrix ι ι ℂ :=
  CStarMatrix.ofMatrix (fun i j => scalarExtract (X.val i j 0 0))

def rightDiagonal (X : matrices (system A) ι) : CStarMatrix ι ι ℂ :=
  CStarMatrix.ofMatrix (fun i j => scalarExtract (X.val i j 1 1))

def offDiagonal (X : matrices (system A) ι) : CStarMatrix ι ι A :=
  CStarMatrix.ofMatrix (fun i j => X.val i j 0 1)

omit [Nontrivial A] in
lemma lower_entry (X : matrices (system A) ι) (hX : 0≤X.val) (i j : ι) :
    X.val i j 1 0=star (X.val j i 0 1) := by
  exact (congrArg (fun Z : CStarMatrix ι ι (CStarMatrix (Fin 2) (Fin 2) A) => Z i j 1 0)
    (IsSelfAdjoint.of_nonneg hX).star_eq).symm

lemma source_block (X : matrices (system A) ι) (hX : 0≤X.val) :
    MatrixGNS.shuffle ι (Fin 2) X.val=
      block (scalarMatrix (leftDiagonal X)) (offDiagonal X) (star (offDiagonal X))
        (scalarMatrix (rightDiagonal X)) := by
  ext i j k l
  rw [MatrixGNS.shuffle_apply]
  fin_cases i <;> fin_cases j
  · exact (scalar_reconstruct00 ⟨X.val k l,X.property k l⟩).symm
  · rfl
  · exact lower_entry X hX k l
  · exact (scalar_reconstruct11 ⟨X.val k l,X.property k l⟩).symm

omit [Nontrivial A] in
lemma output_block (f : A →ₗ[ℂ] B) (X : matrices (system A) ι) (hX : 0≤X.val) :
    MatrixGNS.shuffle ι (Fin 2) (mapMatrix (system A) (systemMap f) X)=
      block (scalarMatrix (leftDiagonal X)) (CStarMatrix.mapₗ f (offDiagonal X))
        (star (CStarMatrix.mapₗ f (offDiagonal X))) (scalarMatrix (rightDiagonal X)) := by
  ext i j k l
  rw [MatrixGNS.shuffle_apply]
  fin_cases i <;> fin_cases j
  · rfl
  · rfl
  · change star (f (star (X.val k l 1 0)))=star (f (X.val l k 0 1))
    rw [lower_entry X hX,star_star]
  · rfl

lemma source_nonneg (X : matrices (system A) ι) (hX : 0≤X.val) :
    0 ≤ block (scalarMatrix (A:=A) (leftDiagonal X)) (offDiagonal X)
      (star (offDiagonal X)) (scalarMatrix (rightDiagonal X)) := by
  rw [←source_block X hX]
  exact map_nonneg (MatrixGNS.shuffle ι (Fin 2)) hX

lemma diagonal_nonneg_pair (X : matrices (system A) ι) (hX : 0≤X.val) :
    0≤leftDiagonal X ∧ 0≤rightDiagonal X := by
  have hblock := source_nonneg X hX
  have hpA : 0 ≤ scalarMatrix (A:=A) (leftDiagonal X) := by
    simpa only [block00] using diagonal_nonneg _ hblock 0
  have hqA : 0 ≤ scalarMatrix (A:=A) (rightDiagonal X) := by
    simpa only [block11] using diagonal_nonneg _ hblock 1
  exact ⟨(@faithfulStar_nonneg_iff
      (CStarMatrix ι ι ℂ) (CStarMatrix ι ι A)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      (scalarMatrix (A:=A)) scalarMatrix_injective _).mp hpA,
    (@faithfulStar_nonneg_iff
      (CStarMatrix ι ι ℂ) (CStarMatrix ι ι A)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      (scalarMatrix (A:=A)) scalarMatrix_injective _).mp hqA⟩

lemma target_nonneg (f : A →ₗ[ℂ] B) (hf : IsCompletelyContractive f)
    (X : matrices (system A) ι) (hX : 0≤X.val) :
    0 ≤ block (scalarMatrix (A:=B) (leftDiagonal X)) (CStarMatrix.mapₗ f (offDiagonal X))
      (star (CStarMatrix.mapₗ f (offDiagonal X))) (scalarMatrix (rightDiagonal X)) := by
  obtain ⟨hp,hq⟩ := diagonal_nonneg_pair X hX
  exact @transfer_nonneg
    (CStarMatrix ι ι A) (CStarMatrix ι ι B) (CStarMatrix ι ι ℂ)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance
    (scalarMatrix (A:=A)) (scalarMatrix (A:=B))
    (CStarMatrix.mapₗ f) (hf ι) (fun c a d => map_scalar_bimodule f c d a)
    (leftDiagonal X) (rightDiagonal X) hp hq (offDiagonal X) (source_nonneg X hX)

lemma output_nonneg (f : A →ₗ[ℂ] B) (hf : IsCompletelyContractive f)
    (X : matrices (system A) ι) (hX : 0≤X.val) :
    0 ≤ mapMatrix (system A) (systemMap f) X := by
  have ho := target_nonneg f hf X hX
  rw [←output_block f X hX] at ho
  simpa only [StarAlgEquiv.symm_apply_apply] using map_nonneg (MatrixGNS.shuffle ι (Fin 2)).symm ho

end MatrixTest

theorem systemMap_completelyPositive [Nontrivial A] (f : A →ₗ[ℂ] B)
    (hf : IsCompletelyContractive f) : IsCompletelyPositive (system A) (systemMap f) := by
  intro ι _ X hX
  exact MatrixTest.output_nonneg f hf X hX

end Kadison.Paulsen

end

end
end

end OAI
