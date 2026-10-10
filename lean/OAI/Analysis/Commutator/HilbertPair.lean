import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

namespace Kadison.HilbertPair

variable (F K : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

abbrev Space := WithLp 2 (F × K)

def left : F →ₗᵢ[ℂ] Space F K where
  toFun x := WithLp.toLp 2 (x,0)
  map_add' x y := by
    apply (WithLp.equiv 2 (F × K)).injective
    simp
  map_smul' z x := by
    apply (WithLp.equiv 2 (F × K)).injective
    simp
  norm_map' x := WithLp.norm_toLp_fst 2 F K x

def right : K →ₗᵢ[ℂ] Space F K where
  toFun x := WithLp.toLp 2 (0,x)
  map_add' x y := by
    apply (WithLp.equiv 2 (F × K)).injective
    simp
  map_smul' z x := by
    apply (WithLp.equiv 2 (F × K)).injective
    simp
  norm_map' x := WithLp.norm_toLp_snd 2 F K x

omit [CompleteSpace F] [CompleteSpace K] in
@[simp] lemma left_apply (x : F) : left F K x=WithLp.toLp 2 (x,0) := rfl

omit [CompleteSpace F] [CompleteSpace K] in
@[simp] lemma right_apply (x : K) : right F K x=WithLp.toLp 2 (0,x) := rfl

lemma left_adjoint : (left F K).toContinuousLinearMap.adjoint=WithLp.fstL 2 ℂ F K := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp [WithLp.prod_inner_apply]

lemma right_adjoint : (right F K).toContinuousLinearMap.adjoint=WithLp.sndL 2 ℂ F K := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp [WithLp.prod_inner_apply]

@[simp] lemma left_adjoint_left :
    (left F K).toContinuousLinearMap.adjoint.comp (left F K).toContinuousLinearMap=1 := by
  rw [left_adjoint]
  ext x
  rfl

@[simp] lemma right_adjoint_right :
    (right F K).toContinuousLinearMap.adjoint.comp (right F K).toContinuousLinearMap=1 := by
  rw [right_adjoint]
  ext x
  rfl

@[simp] lemma left_adjoint_right :
    (left F K).toContinuousLinearMap.adjoint.comp (right F K).toContinuousLinearMap=0 := by
  rw [left_adjoint]
  ext x
  rfl

@[simp] lemma right_adjoint_left :
    (right F K).toContinuousLinearMap.adjoint.comp (left F K).toContinuousLinearMap=0 := by
  rw [right_adjoint]
  ext x
  rfl

end Kadison.HilbertPair

end

end
end

end OAI
