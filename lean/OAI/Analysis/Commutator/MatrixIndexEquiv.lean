import Mathlib
import OAI.Analysis.Commutator.MatrixTowerInclusion

namespace OAI

noncomputable section

section

noncomputable section

open scoped Matrix.Norms.L2Operator

namespace Kadison.MatrixTower

def matrixIndexEquiv {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (e : I ≃ J) : Matrix I I ℂ ≃⋆ₐ[ℂ] Matrix J J ℂ where
  __ := (Matrix.reindexAlgEquiv ℂ ℂ e).toRingEquiv
  map_smul' c a := by ext i j; rfl
  map_star' a := by
    change Matrix.reindex e e a.conjTranspose=(Matrix.reindex e e a).conjTranspose
    exact (Matrix.conjTranspose_reindex e e a).symm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (F : ℕ → Stage M)

def normalizedSize (n : ℕ) : ℕ := Fintype.card (F n).I-1

lemma normalizedSize_succ (n : ℕ) : normalizedSize M F n+1=Fintype.card (F n).I := by
  have h := Fintype.card_pos (α := (F n).I)
  unfold normalizedSize
  omega

def normalizedIndex (n : ℕ) : Fin (normalizedSize M F n+1) ≃ (F n).I :=
  (finCongr (normalizedSize_succ M F n)).trans (Fintype.equivFin (F n).I).symm

def normalizedStage (n : ℕ) : Matrix (Fin (normalizedSize M F n+1)) (Fin (normalizedSize M F n+1)) ℂ →⋆ₐ[ℂ] M :=
  (F n).hom.comp (matrixIndexEquiv (normalizedIndex M F n)).toStarAlgHom

lemma normalizedStage_range (n : ℕ) : (normalizedStage M F n).range=(F n).hom.range := by
  ext a
  constructor
  · rintro ⟨b,rfl⟩
    exact ⟨matrixIndexEquiv (normalizedIndex M F n) b,rfl⟩
  · rintro ⟨b,rfl⟩
    refine ⟨(matrixIndexEquiv (normalizedIndex M F n)).symm b,?_⟩
    change (F n).hom (matrixIndexEquiv (normalizedIndex M F n) ((matrixIndexEquiv (normalizedIndex M F n)).symm b))=_
    rw [StarAlgEquiv.apply_symm_apply]
    rfl

variable [Nontrivial M] (hF : Monotone (fun n => (F n).hom.range))

def normalizedInclusion {n m : ℕ} (h : n ≤ m) :
    Matrix (Fin (normalizedSize M F n+1)) (Fin (normalizedSize M F n+1)) ℂ →⋆ₐ[ℂ]
    Matrix (Fin (normalizedSize M F m+1)) (Fin (normalizedSize M F m+1)) ℂ :=
  (matrixIndexEquiv (normalizedIndex M F m)).symm.toStarAlgHom.comp
    ((stageInclusion M F hF h).comp (matrixIndexEquiv (normalizedIndex M F n)).toStarAlgHom)

lemma normalizedInclusion_commutes {n m : ℕ} (h : n ≤ m) (a) :
    normalizedStage M F m (normalizedInclusion M F hF h a)=normalizedStage M F n a := by
  change (F m).hom (matrixIndexEquiv (normalizedIndex M F m)
    ((matrixIndexEquiv (normalizedIndex M F m)).symm
      (stageInclusion M F hF h (matrixIndexEquiv (normalizedIndex M F n) a))))=_
  rw [StarAlgEquiv.apply_symm_apply,stageInclusion_commutes]
  rfl

end Kadison.MatrixTower

end

end
end

end OAI
