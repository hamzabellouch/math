import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.DimensionDrop.ContinuousBlockSort

namespace OAI

section

noncomputable section
namespace JiangSuConstruction
open scoped CStarAlgebra ComplexOrder

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

def homUnitary (f : A →⋆ₐ[ℂ] B) (u : unitary A) : unitary B :=
  ⟨f (u:A),Unitary.map_mem f u.property⟩
lemma homUnitary_continuous (f : A →⋆ₐ[ℂ] B) : Continuous (homUnitary f) :=
  continuous_induced_rng.mpr ((map_continuous f).comp continuous_subtype_val)
@[simp] lemma homUnitary_one (f : A →⋆ₐ[ℂ] B) : homUnitary f 1=1 := by
  apply Subtype.ext
  exact map_one f
lemma homUnitary_mul (f : A →⋆ₐ[ℂ] B) (u v : unitary A) :
    homUnitary f (u*v)=homUnitary f u*homUnitary f v := by
  apply Subtype.ext
  exact map_mul f _ _
lemma homUnitary_conjugation (f : A →⋆ₐ[ℂ] B) (u : unitary A) (x : A) :
    unitaryConjugation (homUnitary f u) (f x)=f (unitaryConjugation u x) := by
  change f (u:A)*f x*star (f (u:A))=f ((u:A)*x*star (u:A))
  simp only [map_mul,map_star]

variable {I J K H : Type*} [Fintype I] [Fintype J] [Fintype K] [Fintype H]
  [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq H]

def blockUnitary (u : J → unitary (CStarMatrix I I ℂ)) :
    unitary (CStarMatrix (I×J) (I×J) ℂ) :=
  ⟨blockDiagonalHom (fun j => (u j:CStarMatrix I I ℂ)),by
    constructor
    · change star (blockDiagonalHom _)*blockDiagonalHom _=1
      rw [←map_star,←map_mul]
      have h : (star (fun j => (u j:CStarMatrix I I ℂ)))*(fun j => (u j:CStarMatrix I I ℂ))=1 := by
        funext j
        exact (u j).property.1
      rw [h,map_one]
    · change blockDiagonalHom _*star (blockDiagonalHom _)=1
      rw [←map_star,←map_mul]
      have h : (fun j => (u j:CStarMatrix I I ℂ))*star (fun j => (u j:CStarMatrix I I ℂ))=1 := by
        funext j
        exact (u j).property.2
      rw [h,map_one]⟩
lemma blockUnitary_continuous : Continuous (blockUnitary (I := I) (J := J)) :=
  continuous_induced_rng.mpr (blockDiagonalHom_continuous.comp
    (continuous_pi fun j => continuous_subtype_val.comp (continuous_apply j)))
lemma blockUnitary_conjugation (u : J → unitary (CStarMatrix I I ℂ))
    (x : J → CStarMatrix I I ℂ) :
    blockDiagonalHom (fun j => unitaryConjugation (u j) (x j))=
      unitaryConjugation (A := CStarMatrix (I×J) (I×J) ℂ)
        (blockUnitary (I := I) (J := J) u) (blockDiagonalHom x) := by
  change blockDiagonalHom ((fun j => (u j:CStarMatrix I I ℂ))*x*
    star (fun j => (u j:CStarMatrix I I ℂ)))=_
  rw [map_mul,map_mul,map_star]
  rfl
lemma block_reindex (e : I≃H) (x : J → CStarMatrix I I ℂ) :
    blockDiagonalHom (fun j => CStarMatrix.reindexₐ ℂ ℂ e (x j))=
      CStarMatrix.reindexₐ ℂ ℂ (Equiv.prodCongr e (Equiv.refl J)) (blockDiagonalHom x) := by
  ext ⟨i,j⟩ ⟨k,l⟩
  change Matrix.blockDiagonal (fun j => Matrix.reindex e e (CStarMatrix.ofMatrix.symm (x j))) (i,j) (k,l)=
    Matrix.blockDiagonal (fun j => CStarMatrix.ofMatrix.symm (x j)) (e.symm i,j) (e.symm k,l)
  simp only [Matrix.blockDiagonal_apply,Matrix.reindex_apply]
  split_ifs <;> rfl
lemma block_assoc (x : J×K → CStarMatrix I I ℂ) :
    blockDiagonalHom (fun k => blockDiagonalHom (fun j => x (j,k)))=
      CStarMatrix.reindexₐ ℂ ℂ (Equiv.prodAssoc I J K).symm (blockDiagonalHom x) := by
  ext ⟨⟨i,j⟩,k⟩ ⟨⟨a,b⟩,c⟩
  change Matrix.blockDiagonal (fun k => Matrix.blockDiagonal (fun j => CStarMatrix.ofMatrix.symm (x (j,k))))
    ((i,j),k) ((a,b),c)=Matrix.blockDiagonal (fun jk => CStarMatrix.ofMatrix.symm (x jk)) (i,(j,k)) (a,(b,c))
  simp only [Matrix.blockDiagonal_apply,Prod.mk.injEq]
  split_ifs <;> simp_all
lemma block_punit (x : CStarMatrix I I ℂ) :
    CStarMatrix.reindexₐ ℂ ℂ (Equiv.prodPUnit I) (blockDiagonalHom (fun _ : PUnit.{1} => x))=x := by
  ext i j
  change Matrix.blockDiagonal (fun _ : PUnit.{1} => CStarMatrix.ofMatrix.symm x) (i,PUnit.unit) (j,PUnit.unit)=x i j
  simp [Matrix.blockDiagonal_apply]

variable {L : Type*} [Fintype L] [DecidableEq L]

lemma diagonalization_comp (u : unitary (CStarMatrix H H ℂ))
    (v : J → unitary (CStarMatrix K K ℂ)) (e : I×L≃K) (d : K×J≃H)
    (x : L×J → CStarMatrix I I ℂ) :
    unitaryConjugation u (CStarMatrix.reindexₐ ℂ ℂ d
      (blockDiagonalHom (fun j => unitaryConjugation (v j)
        (CStarMatrix.reindexₐ ℂ ℂ e (blockDiagonalHom (fun i => x (i,j)))))))=
    unitaryConjugation (u*homUnitary (CStarMatrix.reindexₐ ℂ ℂ d).toStarAlgHom (blockUnitary v))
      (CStarMatrix.reindexₐ ℂ ℂ (((Equiv.prodAssoc I L J).symm.trans
        (Equiv.prodCongr e (Equiv.refl J))).trans d) (blockDiagonalHom x)) := by
  rw [blockUnitary_conjugation]
  change unitaryConjugation u ((CStarMatrix.reindexₐ ℂ ℂ d).toStarAlgHom
    (unitaryConjugation (A := CStarMatrix (K×J) (K×J) ℂ) (blockUnitary v) _))=_
  rw [←homUnitary_conjugation,←unitaryConjugation_mul]
  apply congrArg (unitaryConjugation _)
  rw [block_reindex,block_assoc]
  rfl

end JiangSuConstruction

end
end

end OAI
