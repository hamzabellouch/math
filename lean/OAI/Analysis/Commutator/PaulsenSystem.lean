import Mathlib
import OAI.Analysis.Commutator.TwoByTwoPositive
import OAI.Analysis.Commutator.MatrixScalar

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators ComplexOrder

namespace Kadison.Paulsen

open CStarBlock MatrixScalar

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

local instance paulsenSystemDecidableEqFinTwo : DecidableEq (Fin 2) := Classical.decEq (Fin 2)

def system (A : Type*) [CStarAlgebra A] : Submodule ℂ (CStarMatrix (Fin 2) (Fin 2) A) where
  carrier := {X | ∃ a b : ℂ,X 0 0=algebraMap ℂ A a ∧ X 1 1=algebraMap ℂ A b}
  zero_mem' := ⟨0,0,by simp,by simp⟩
  add_mem' := by
    rintro X Y ⟨a,b,ha,hb⟩ ⟨c,d,hc,hd⟩
    exact ⟨a+c,b+d,by simpa only [map_add,CStarMatrix.add_apply] using congrArg₂ (·+·) ha hc,
      by simpa only [map_add,CStarMatrix.add_apply] using congrArg₂ (·+·) hb hd⟩
  smul_mem' := by
    rintro c X ⟨a,b,ha,hb⟩
    refine ⟨c*a,c*b,?_,?_⟩
    · change c • X 0 0=algebraMap ℂ A (c*a)
      rw [ha,map_mul,Algebra.smul_def]
    · change c • X 1 1=algebraMap ℂ A (c*b)
      rw [hb,map_mul,Algebra.smul_def]

lemma one_mem : (1 : CStarMatrix (Fin 2) (Fin 2) A)∈system A :=
  ⟨1,1,by simp,by simp⟩

lemma star_mem (X : CStarMatrix (Fin 2) (Fin 2) A) (hX : X∈system A) : star X∈system A := by
  obtain ⟨a,b,ha,hb⟩ := hX
  refine ⟨star a,star b,?_,?_⟩
  · change star (X 0 0)=_
    rw [ha]; simp [Algebra.algebraMap_eq_smul_one]
  · change star (X 1 1)=_
    rw [hb]; simp [Algebra.algebraMap_eq_smul_one]

def scalarExtract : A →ₗ[ℂ] ℂ := (Algebra.linearMap ℂ A).leftInverse

lemma scalarExtract_scalar [Nontrivial A] (c : ℂ) : scalarExtract (algebraMap ℂ A c)=c :=
  LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr (algebraMap ℂ A).injective) c

lemma scalar_reconstruct00 [Nontrivial A] (X : system A) :
    algebraMap ℂ A (scalarExtract (X.val 0 0))=X.val 0 0 := by
  obtain ⟨a,b,ha,hb⟩ := X.property
  rw [ha,scalarExtract_scalar]

lemma scalar_reconstruct11 [Nontrivial A] (X : system A) :
    algebraMap ℂ A (scalarExtract (X.val 1 1))=X.val 1 1 := by
  obtain ⟨a,b,ha,hb⟩ := X.property
  rw [hb,scalarExtract_scalar]

def sharp (f : A →ₗ[ℂ] B) : A →ₗ[ℂ] B where
  toFun a := star (f (star a))
  map_add' a b := by simp only [star_add,map_add]
  map_smul' c a := by simp only [star_smul,map_smul,star_star,RingHom.id_apply]

def systemMap (f : A →ₗ[ℂ] B) : system A →ₗ[ℂ] CStarMatrix (Fin 2) (Fin 2) B where
  toFun X := block (algebraMap ℂ B (scalarExtract (X.val 0 0))) (f (X.val 0 1))
    (sharp f (X.val 1 0)) (algebraMap ℂ B (scalarExtract (X.val 1 1)))
  map_add' X Y := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [block,Submodule.coe_add,CStarMatrix.add_apply,map_add]
  map_smul' c X := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [block,CStarMatrix.smul_apply,map_smul,
        RingHom.id_apply,Algebra.algebraMap_eq_smul_one,smul_smul]

@[simp] lemma systemMap00 (f : A →ₗ[ℂ] B) (X : system A) :
    systemMap f X 0 0=algebraMap ℂ B (scalarExtract (X.val 0 0)) := rfl

@[simp] lemma systemMap01 (f : A →ₗ[ℂ] B) (X : system A) : systemMap f X 0 1=f (X.val 0 1) := rfl

@[simp] lemma systemMap10 (f : A →ₗ[ℂ] B) (X : system A) :
    systemMap f X 1 0=star (f (star (X.val 1 0))) := rfl

@[simp] lemma systemMap11 (f : A →ₗ[ℂ] B) (X : system A) :
    systemMap f X 1 1=algebraMap ℂ B (scalarExtract (X.val 1 1)) := rfl

lemma systemMap_one [Nontrivial A] (f : A →ₗ[ℂ] B) : systemMap f ⟨1,one_mem⟩=1 := by
  have he : scalarExtract (1:A)=1 := by simpa only [map_one] using scalarExtract_scalar (A:=A) 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [systemMap,he,sharp]

end Kadison.Paulsen

end

end
end

end OAI
