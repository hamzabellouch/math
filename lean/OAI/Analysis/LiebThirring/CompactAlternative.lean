import OAI.Analysis.LiebThirring.PotentialCompactness

namespace OAI

universe u190


noncomputable section
namespace SharpLiebThirring.OperatorProof
open Module

/-- The Fredholm alternative, transported through an arbitrary bounded isomorphism. -/
lemma compact_perturbation_alternative {E : Type u190} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (B : E ≃L[ℂ] E) (C : E →L[ℂ] E)
    (hC : IsCompactOperator C) :
    (∃ u : E, u ≠ 0 ∧ B u-C u = 0) ∨
      Function.Bijective (B.toContinuousLinearMap-C) := by
  let K : E →L[ℂ] E := B.symm.toContinuousLinearMap.comp C
  have hK : IsCompactOperator K := hC.clm_comp B.symm.toContinuousLinearMap
  rcases hK.hasEigenvalue_or_mem_resolventSet (by norm_num : (1:ℂ) ≠ 0) with he | hr
  · obtain ⟨u,hu⟩ := he.exists_hasEigenvector
    have hk := hu.apply_eq_smul
    change K u = (1:ℂ) • u at hk
    simp only [one_smul] at hk
    have hb : C u = B u := by
      have hh := congrArg B hk
      simpa only [K,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.apply_symm_apply] using hh
    exact Or.inl ⟨u,hu.2,sub_eq_zero.mpr hb.symm⟩
  · have hb : Function.Bijective (1-K : E →L[ℂ] E) := by
      rw [spectrum.mem_resolventSet_iff,ContinuousLinearMap.isUnit_iff_bijective] at hr
      simpa only [map_one] using hr
    have hcomp : (B.toContinuousLinearMap-C : E → E) =
        B ∘ ((1-K : E →L[ℂ] E) : E → E) := by
      funext u
      change B u-C u = B (u-B.symm (C u))
      rw [map_sub,ContinuousLinearEquiv.apply_symm_apply]
    right
    change Function.Bijective (B.toContinuousLinearMap-C : E → E)
    rw [hcomp]
    exact B.bijective.comp hb

end SharpLiebThirring.OperatorProof

end

end OAI
