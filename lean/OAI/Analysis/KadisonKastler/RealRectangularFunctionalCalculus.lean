import OAI.Analysis.KadisonKastler.RectangularFunctionalCalculus
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.InnerProductSpace.StarOrder

namespace OAI

/-! # Real functional calculus through a rectangular intertwiner -/

namespace KadisonKastler

open scoped InnerProductSpace

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem real_cfc_rectangular_intertwines
    (a : K →L[ℂ] K) (b : H →L[ℂ] H) (T : H →L[ℂ] K)
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (hT : a.comp T = T.comp b) (f : ℝ → ℝ)
    (hfa : ContinuousOn f (spectrum ℝ a)) (hfb : ContinuousOn f (spectrum ℝ b)) :
    (cfc f a).comp T = T.comp (cfc f b) := by
  let S := spectrum ℝ a ∪ spectrum ℝ b
  have hS : IsCompact S := (spectrum.isCompact a).union (spectrum.isCompact b)
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let φ := cfcHomSuperset ha (Set.subset_union_left : spectrum ℝ a ⊆ S)
  let ψ := cfcHomSuperset hb (Set.subset_union_right : spectrum ℝ b ⊆ S)
  have hφ : Continuous φ := cfcHomSuperset_continuous _ _
  have hψ : Continuous ψ := cfcHomSuperset_continuous _ _
  have he (g : C(S, ℝ)) : (φ g).comp T = T.comp (ψ g) := by
    induction g using ContinuousMap.induction_on_of_compact with
    | const z =>
      change (φ (algebraMap ℝ _ z)).comp T = T.comp (ψ (algebraMap ℝ _ z))
      rw [AlgHomClass.commutes, AlgHomClass.commutes]
      ext x
      simp
    | id =>
      change (cfcHomSuperset ha _ (.restrict S (.id ℝ))).comp T =
        T.comp (cfcHomSuperset hb _ (.restrict S (.id ℝ)))
      rw [cfcHomSuperset_id, cfcHomSuperset_id]
      exact hT
    | star_id =>
      rw [map_star, map_star]
      change (star (cfcHomSuperset ha _ (.restrict S (.id ℝ)))).comp T =
        T.comp (star (cfcHomSuperset hb _ (.restrict S (.id ℝ))))
      rw [cfcHomSuperset_id, cfcHomSuperset_id, ha.star_eq, hb.star_eq]
      exact hT
    | add g h hg hh =>
      simp only [map_add, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, hg, hh]
    | mul g h hg hh =>
      change (φ (g * h)).comp T = T.comp (ψ (g * h))
      rw [map_mul, map_mul]
      change (φ g).comp ((φ h).comp T) = T.comp ((ψ g).comp (ψ h))
      rw [hh, ← ContinuousLinearMap.comp_assoc, hg, ContinuousLinearMap.comp_assoc]
    | frequently g hg =>
      exact hg.mem_of_closed (isClosed_eq (hφ.clm_comp continuous_const)
        (continuous_const.clm_comp hψ))
  have hf : ContinuousOn f S := hfa.union_of_isClosed hfb
    (spectrum.isCompact a).isClosed (spectrum.isCompact b).isClosed
  rw [cfc_apply f a ha hfa, cfc_apply f b hb hfb]
  exact he ⟨_, hf.domRestrict⟩

theorem sqrt_rectangular_intertwines
    (a : K →L[ℂ] K) (b : H →L[ℂ] H) (T : H →L[ℂ] K)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hT : a.comp T = T.comp b) :
    (CFC.sqrt a).comp T = T.comp (CFC.sqrt b) := by
  rw [CFC.sqrt_eq_real_sqrt a ha, CFC.sqrt_eq_real_sqrt b hb, cfcₙ_eq_cfc, cfcₙ_eq_cfc]
  exact real_cfc_rectangular_intertwines a b T ha.isSelfAdjoint hb.isSelfAdjoint hT
    Real.sqrt Real.continuous_sqrt.continuousOn Real.continuous_sqrt.continuousOn

end
end KadisonKastler

end OAI
