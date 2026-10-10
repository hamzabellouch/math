import OAI.Analysis.Pureness.Stabilization.PositiveCore
import OAI.Analysis.Pureness.Stabilization.MatrixBlockNorm

namespace OAI
noncomputable section
open scoped CStarAlgebra
namespace CuntzTrace
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def matrixSwapPermutation (n : ℕ) : Equiv.Perm (Fin (n*2)) :=
  finProdFinEquiv.symm.trans (((Equiv.refl (Fin n)).prodCongr (Equiv.swap (0 : Fin 2) 1)).trans finProdFinEquiv)

lemma matrixSwapPermutation_apply (n : ℕ) (i : Fin n) (r : Fin 2) :
    matrixSwapPermutation n (finProdFinEquiv (i,r)) = finProdFinEquiv (i,Equiv.swap 0 1 r) := by
  simp [matrixSwapPermutation]

omit [PartialOrder A] [StarOrderedRing A] in
theorem matrixInterleave_swap (n : ℕ) (M N : FinMatrix A n) :
    matrixPermute (matrixSwapPermutation n) (matrixInterleave n (M,N)) = matrixInterleave n (N,M) := by
  apply CStarMatrix.ext; intro i j
  obtain ⟨i,rfl⟩ := (matrixSwapPermutation n).surjective i
  obtain ⟨j,rfl⟩ := (matrixSwapPermutation n).surjective j
  rw [matrixPermute_entry]
  obtain ⟨⟨p,r⟩,rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨q,s⟩,rfl⟩ := finProdFinEquiv.surjective j
  rw [matrixSwapPermutation_apply,matrixSwapPermutation_apply,matrixInterleave_entry,matrixInterleave_entry]
  fin_cases r <;> fin_cases s <;> simp

def matrixBlockSwapHom : (MatrixLimit A × MatrixLimit A) →⋆ₙₐ[ℂ] MatrixLimit A :=
  matrixBlockHom.comp ((NonUnitalStarAlgHom.snd ℂ _ _).prod (NonUnitalStarAlgHom.fst ℂ _ _))

lemma matrixBlockPositive_stage (n : ℕ) (M N : Positive (FinMatrix A n)) :
    matrixBlockPositive (Positive.map (matrixLimitStage n) M) (Positive.map (matrixLimitStage n) N) =
      Positive.map (matrixLimitStage (n*2)) (Positive.map (matrixInterleave n) (positiveProduct M N)) :=
  Subtype.ext (matrixBlockHom_stage n (M.1,N.1))

theorem matrixBlockPositive_comm (a b : Positive (MatrixLimit A)) :
    CuntzClass.mk (matrixBlockPositive a b) = CuntzClass.mk (matrixBlockPositive b a) := by
  let S := (matrixPositiveCore (A := A)).prod (matrixPositiveCore (A := A))
  apply S.maps_eq matrixBlockHom matrixBlockSwapHom ?_ (positiveProduct a b)
  intro c hc
  let a : Positive (MatrixLimit A) := Positive.map (NonUnitalStarAlgHom.fst ℂ _ _) c
  let b : Positive (MatrixLimit A) := Positive.map (NonUnitalStarAlgHom.snd ℂ _ _) c
  obtain ⟨n,M,N,hM,hN⟩ := matrixPositiveCore_common a b hc.1 hc.2
  change CuntzClass.mk (matrixBlockPositive a b) = CuntzClass.mk (matrixBlockPositive b a)
  rw [← hM,← hN,matrixBlockPositive_stage,matrixBlockPositive_stage]
  have he : Positive.map (matrixPermute (matrixSwapPermutation n))
      (Positive.map (matrixInterleave n) (positiveProduct M N)) =
      Positive.map (matrixInterleave n) (positiveProduct N M) :=
    Subtype.ext (matrixInterleave_swap n M.1 N.1)
  have h := matrixPermute_cuntzClass (matrixSwapPermutation n)
    (Positive.map (matrixInterleave n) (positiveProduct M N))
  rw [he] at h
  exact (congrArg (CuntzClass.map (matrixLimitStage (A := A) (n*2))) h).symm

theorem CuntzClass.matrixAdd_comm (x y : CuntzClass (MatrixLimit A)) : matrixAdd x y = matrixAdd y x := by
  induction x using Quotient.inductionOn with | h a =>
  induction y using Quotient.inductionOn with | h b =>
  exact matrixBlockPositive_comm a b
end CuntzTrace

end

end OAI
