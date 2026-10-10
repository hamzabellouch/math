import OAI.Analysis.KadisonKastler.Algebra
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

namespace OAI

/-! # Continuous functional calculus through a rectangular intertwiner -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Functional calculus preserves a bounded intertwiner of selfadjoint operators,
even when the two operators act on different Hilbert spaces. -/
theorem cfc_rectangular_intertwines
    (a : K →L[ℂ] K) (b : H →L[ℂ] H) (T : H →L[ℂ] K)
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (hT : a.comp T = T.comp b) (f : ℂ → ℂ)
    (hfa : ContinuousOn f (spectrum ℂ a)) (hfb : ContinuousOn f (spectrum ℂ b)) :
    (cfc f a).comp T = T.comp (cfc f b) := by
  let S := spectrum ℂ a ∪ spectrum ℂ b
  have hS : IsCompact S := (spectrum.isCompact a).union (spectrum.isCompact b)
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let φ := cfcHomSuperset ha.isStarNormal (Set.subset_union_left : spectrum ℂ a ⊆ S)
  let ψ := cfcHomSuperset hb.isStarNormal (Set.subset_union_right : spectrum ℂ b ⊆ S)
  have hφ : Continuous φ := cfcHomSuperset_continuous _ _
  have hψ : Continuous ψ := cfcHomSuperset_continuous _ _
  have he (g : C(S, ℂ)) : (φ g).comp T = T.comp (ψ g) := by
    induction g using ContinuousMap.induction_on_of_compact with
    | const z =>
      change (φ (algebraMap ℂ _ z)).comp T = T.comp (ψ (algebraMap ℂ _ z))
      rw [AlgHomClass.commutes, AlgHomClass.commutes]
      ext x
      simp
    | id =>
      change (cfcHomSuperset ha.isStarNormal _ (.restrict S (.id ℂ))).comp T =
        T.comp (cfcHomSuperset hb.isStarNormal _ (.restrict S (.id ℂ)))
      rw [cfcHomSuperset_id, cfcHomSuperset_id]
      exact hT
    | star_id =>
      rw [map_star, map_star]
      change (star (cfcHomSuperset ha.isStarNormal _ (.restrict S (.id ℂ)))).comp T =
        T.comp (star (cfcHomSuperset hb.isStarNormal _ (.restrict S (.id ℂ))))
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
  have hf : ContinuousOn f S := hfa.union_of_isClosed hfb (spectrum.isCompact a).isClosed (spectrum.isCompact b).isClosed
  rw [cfc_apply f a ha.isStarNormal hfa, cfc_apply f b hb.isStarNormal hfb]
  exact he ⟨_, hf.domRestrict⟩

end

end KadisonKastler

end OAI
