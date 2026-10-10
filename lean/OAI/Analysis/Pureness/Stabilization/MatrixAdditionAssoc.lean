import OAI.Analysis.Pureness.Stabilization.MatrixTripleLayout
import OAI.Analysis.Pureness.Stabilization.MatrixAdditionComm

namespace OAI
noncomputable section
open scoped CStarAlgebra
namespace CuntzTrace
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def matrixAssocLeftHom : ((MatrixLimit A × MatrixLimit A) × MatrixLimit A) →⋆ₙₐ[ℂ] MatrixLimit A :=
  matrixBlockHom.comp ((matrixBlockHom.comp (NonUnitalStarAlgHom.fst ℂ _ _)).prod
    (NonUnitalStarAlgHom.snd ℂ _ _))

def matrixAssocRightHom : ((MatrixLimit A × MatrixLimit A) × MatrixLimit A) →⋆ₙₐ[ℂ] MatrixLimit A :=
  matrixBlockHom.comp (((NonUnitalStarAlgHom.fst ℂ _ _).comp (NonUnitalStarAlgHom.fst ℂ _ _)).prod
    (matrixBlockHom.comp (((NonUnitalStarAlgHom.snd ℂ _ _).comp (NonUnitalStarAlgHom.fst ℂ _ _)).prod
      (NonUnitalStarAlgHom.snd ℂ _ _))))

lemma matrixPositiveCore_common_three (a b c : Positive (MatrixLimit A))
    (ha : a ∈ matrixPositiveCore.carrier) (hb : b ∈ matrixPositiveCore.carrier)
    (hc : c ∈ matrixPositiveCore.carrier) :
    ∃ (n : ℕ) (M N P : Positive (FinMatrix A n)),
      Positive.map (matrixLimitStage n) M = a ∧ Positive.map (matrixLimitStage n) N = b ∧
      Positive.map (matrixLimitStage n) P = c := by
  obtain ⟨n,M,N,hM,hN⟩ := matrixPositiveCore_common a b ha hb
  obtain ⟨m,P,hP⟩ := hc
  refine ⟨max n m,Positive.map (matrixInclusion (le_max_left n m)) M,
    Positive.map (matrixInclusion (le_max_left n m)) N,
    Positive.map (matrixInclusion (le_max_right n m)) P,?_,?_,?_⟩
  · exact (Subtype.ext (matrixLimitStage_compatible _ _)).trans hM
  · exact (Subtype.ext (matrixLimitStage_compatible _ _)).trans hN
  · exact (Subtype.ext (matrixLimitStage_compatible _ _)).trans hP

lemma matrixTriple_cuntzClass (n : ℕ) (M N P : Positive (FinMatrix A n)) :
    CuntzClass.mk (matrixBlockPositive
      (matrixBlockPositive (Positive.map (matrixLimitStage n) M) (Positive.map (matrixLimitStage n) N))
      (Positive.map (matrixLimitStage n) P)) =
    CuntzClass.mk (matrixBlockPositive (Positive.map (matrixLimitStage n) M)
      (matrixBlockPositive (Positive.map (matrixLimitStage n) N) (Positive.map (matrixLimitStage n) P))) := by
  let h : n ≤ n*2 := by omega
  let L := Positive.map (matrixInterleave (n*2))
    (positiveProduct (Positive.map (matrixInterleave n) (positiveProduct M N))
      (Positive.map (matrixInclusion h) P))
  let R := Positive.map (matrixInterleave (n*2))
    (positiveProduct (Positive.map (matrixInclusion h) M)
      (Positive.map (matrixInterleave n) (positiveProduct N P)))
  have hL : matrixBlockPositive
      (matrixBlockPositive (Positive.map (matrixLimitStage n) M) (Positive.map (matrixLimitStage n) N))
      (Positive.map (matrixLimitStage n) P) = Positive.map (matrixLimitStage ((n*2)*2)) L := by
    rw [matrixBlockPositive_stage]
    have he : Positive.map (matrixLimitStage n) P =
        Positive.map (matrixLimitStage (n*2)) (Positive.map (matrixInclusion h) P) :=
      (Subtype.ext (matrixLimitStage_compatible h P.1)).symm
    rw [he,matrixBlockPositive_stage]
  have hR : matrixBlockPositive (Positive.map (matrixLimitStage n) M)
      (matrixBlockPositive (Positive.map (matrixLimitStage n) N) (Positive.map (matrixLimitStage n) P)) =
      Positive.map (matrixLimitStage ((n*2)*2)) R := by
    rw [matrixBlockPositive_stage]
    have he : Positive.map (matrixLimitStage n) M =
        Positive.map (matrixLimitStage (n*2)) (Positive.map (matrixInclusion h) M) :=
      (Subtype.ext (matrixLimitStage_compatible h M.1)).symm
    rw [he,matrixBlockPositive_stage]
  rw [hL,hR]
  obtain ⟨e,he⟩ := matrixTriple_permutation n M.1 N.1 P.1
  have he' : Positive.map (matrixPermute e) L = R := Subtype.ext he
  have hc := matrixPermute_cuntzClass e L
  rw [he'] at hc
  exact (congrArg (CuntzClass.map (matrixLimitStage (A := A) ((n*2)*2))) hc).symm

theorem matrixBlockPositive_assoc (a b c : Positive (MatrixLimit A)) :
    CuntzClass.mk (matrixBlockPositive (matrixBlockPositive a b) c) =
      CuntzClass.mk (matrixBlockPositive a (matrixBlockPositive b c)) := by
  let S := ((matrixPositiveCore (A := A)).prod (matrixPositiveCore (A := A))).prod (matrixPositiveCore (A := A))
  apply S.maps_eq matrixAssocLeftHom matrixAssocRightHom ?_ ⟨((a.1,b.1),c.1),⟨a.2,b.2⟩,c.2⟩
  intro x hx
  let a : Positive (MatrixLimit A) := ⟨x.1.1.1,x.2.1.1⟩
  let b : Positive (MatrixLimit A) := ⟨x.1.1.2,x.2.1.2⟩
  let c : Positive (MatrixLimit A) := ⟨x.1.2,x.2.2⟩
  obtain ⟨n,M,N,P,hM,hN,hP⟩ := matrixPositiveCore_common_three a b c hx.1.1 hx.1.2 hx.2
  change CuntzClass.mk (matrixBlockPositive (matrixBlockPositive a b) c) =
    CuntzClass.mk (matrixBlockPositive a (matrixBlockPositive b c))
  rw [← hM,← hN,← hP]
  exact matrixTriple_cuntzClass n M N P

theorem CuntzClass.matrixAdd_assoc (x y z : CuntzClass (MatrixLimit A)) :
    matrixAdd (matrixAdd x y) z = matrixAdd x (matrixAdd y z) := by
  induction x using Quotient.inductionOn with | h a =>
  induction y using Quotient.inductionOn with | h b =>
  induction z using Quotient.inductionOn with | h c =>
  exact matrixBlockPositive_assoc a b c

namespace CuntzClass
instance : Add (CuntzClass (MatrixLimit A)) := ⟨matrixAdd⟩
instance matrixAddCommMonoid : AddCommMonoid (CuntzClass (MatrixLimit A)) where
  add_assoc := matrixAdd_assoc
  zero_add := zero_matrixAdd
  add_zero := matrixAdd_zero
  add_comm := matrixAdd_comm
  nsmul := nsmulRec
end CuntzClass
end CuntzTrace

end

end OAI
