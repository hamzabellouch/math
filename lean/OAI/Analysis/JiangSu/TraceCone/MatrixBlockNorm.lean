import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.TraceCone.CuntzDenseMaps

namespace OAI


noncomputable section
open scoped Topology CStarAlgebra

namespace TraceCone
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma matrixBlockHom_stage (n : ℕ) (P : FinMatrix A n × FinMatrix A n) :
    matrixBlockHom (matrixLimitStage n P.1,matrixLimitStage n P.2) = matrixLimitBlock n P := by
  change matrixEven (matrixLimitStage n P.1) + matrixOdd (matrixLimitStage n P.2) = _
  rw [matrixEven_stage,matrixOdd_stage,← map_add]
  congr 1
  simp

private lemma matrixBlockStarHom_continuous {D B : Type*} [NonUnitalCStarAlgebra D] [NonUnitalCStarAlgebra B]
    (f : D →⋆ₙₐ[ℂ] B) : Continuous f := by
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro a b
  simpa only [dist_eq_norm,← map_sub,NNReal.coe_one,one_mul] using
    NonUnitalStarAlgHom.norm_apply_le f (a-b)

theorem matrixBlockHom_norm (x y : MatrixLimit A) : ‖matrixBlockHom (x,y)‖ = max ‖x‖ ‖y‖ := by
  refine finiteMatrixSubalgebra_dense.induction_on₂ ?_ ?_ x y
  · exact isClosed_eq (matrixBlockStarHom_continuous matrixBlockHom).norm
      ((continuous_fst.norm).max continuous_snd.norm)
  · intro u v
    obtain ⟨n,M,N,hu,hv⟩ := finiteMatrix_common_stage u v
    rw [← hu,← hv]
    change ‖matrixBlockHom (matrixLimitStage n M,matrixLimitStage n N)‖ =
      max ‖matrixLimitStage n M‖ ‖matrixLimitStage n N‖
    rw [matrixBlockHom_stage n (M,N),matrixLimitBlock_norm,matrixLimitStage_norm,matrixLimitStage_norm]

theorem matrixBlockHom_isometry : Isometry (matrixBlockHom (A := A)) :=
  AddMonoidHomClass.isometry_of_norm _ (fun P => matrixBlockHom_norm P.1 P.2)

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
  induction x using Quotient.inductionOn with
  | h leftPositive =>
    induction y using Quotient.inductionOn with
    | h rightPositive =>
      exact matrixBlockPositive_comm leftPositive rightPositive


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
  induction x using Quotient.inductionOn with
  | h firstPositive =>
    induction y using Quotient.inductionOn with
    | h secondPositive =>
      induction z using Quotient.inductionOn with
      | h thirdPositive =>
        exact matrixBlockPositive_assoc firstPositive secondPositive thirdPositive

namespace CuntzClass
instance : Add (CuntzClass (MatrixLimit A)) := ⟨matrixAdd⟩
instance matrixAddCommMonoid : AddCommMonoid (CuntzClass (MatrixLimit A)) where
  add_assoc := matrixAdd_assoc
  zero_add := zero_matrixAdd
  add_zero := matrixAdd_zero
  add_comm := matrixAdd_comm
  nsmul := nsmulRec
end CuntzClass
end TraceCone
end

end OAI
