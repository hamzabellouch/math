import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace CStarAlgebra

namespace Kadison.CbFactor

variable {A H K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma gram_strictlyPositive (L : K →L[ℂ] H) (W : H →L[ℂ] K)
    (hLW : L.comp W=1) : IsStrictlyPositive (L.comp L.adjoint) := by
  let T := W.comp W.adjoint
  let c : ℝ := ‖T‖+1
  have hc : 0<c := by dsimp [c]; positivity
  have hT : T≤c • (1 : K →L[ℂ] K) := by
    have h := (ContinuousLinearMap.isPositive_self_comp_adjoint W).isSelfAdjoint.le_algebraMap_norm_self
    rw [Algebra.algebraMap_eq_smul_one] at h
    exact h.trans (smul_le_smul_of_nonneg_right (by dsimp [c]; linarith) zero_le_one)
  have hp := (ContinuousLinearMap.le_def.mp hT).conj_adjoint L
  have hId : L.comp (T.comp L.adjoint)=1 := by
    dsimp [T]
    rw [←ContinuousLinearMap.comp_assoc,←ContinuousLinearMap.comp_assoc,hLW]
    have hadj := congrArg ContinuousLinearMap.adjoint hLW
    simp only [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_one] at hadj
    simpa [ContinuousLinearMap.one_def] using hadj
  have hpos : (c • L.comp L.adjoint-1).IsPositive := by
    simpa only [ContinuousLinearMap.comp_sub,ContinuousLinearMap.sub_comp,
      ContinuousLinearMap.comp_smul,ContinuousLinearMap.smul_comp,
      ContinuousLinearMap.one_def,ContinuousLinearMap.comp_id,ContinuousLinearMap.id_comp,
      ContinuousLinearMap.comp_assoc,hId] using hp
  have hle : (1 : H →L[ℂ] H)≤c • L.comp L.adjoint :=
    ContinuousLinearMap.le_def.mpr hpos
  have hbound : c⁻¹ • (1 : H →L[ℂ] H)≤L.comp L.adjoint := by
    have := smul_le_smul_of_nonneg_left hle (inv_nonneg.mpr hc.le)
    simpa only [smul_smul,inv_mul_cancel₀ hc.ne',one_smul] using this
  exact (IsStrictlyPositive.smul (inv_pos.mpr hc) isStrictlyPositive_one).of_le hbound

variable (π : A →ₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
  (L : K →L[ℂ] H) (hint : ∀ a : A,(π a).comp L=L.comp (ρ a))

include hint in
lemma gram_intertwines (a : A) :
    π a * (L.comp L.adjoint)=(L.comp L.adjoint) * star (π (star a)) := by
  have h := congrArg ContinuousLinearMap.adjoint (hint (star a))
  simp only [ContinuousLinearMap.adjoint_comp,map_star,
    ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_adjoint] at h
  change (π a).comp (L.comp L.adjoint)=(L.comp L.adjoint).comp _
  rw [←ContinuousLinearMap.comp_assoc,hint a,ContinuousLinearMap.comp_assoc,
    ←h,←ContinuousLinearMap.comp_assoc]
  rfl

end Kadison.CbFactor

end

end
end

end OAI
