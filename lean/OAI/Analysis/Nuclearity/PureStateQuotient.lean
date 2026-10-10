import OAI.Analysis.Nuclearity.PositiveStateQuotient
import OAI.Analysis.JiangSu.Excision.PureStateCarrier

namespace OAI

/-! Positive decompositions of a pulled-back pure state are trivial.
This supplies the face argument for pure states on represented quotients. -/

noncomputable section
open scoped ComplexOrder

namespace WeakPureInfiniteness

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

theorem pure_pullback_positive_summand (q : A →⋆ₐ[ℂ] B) (hq : Function.Surjective q)
    (f : B →ₚ[ℂ] ℂ) (hf : f 1 = 1)
    (hp : PureStateExcision.ofPositiveState f hf ∈
      (PureStateExcision.realStateCarrier (A := B)).extremePoints ℝ)
    (g h : A →ₚ[ℂ] ℂ) {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hg : g 1 = (t : ℂ)) (hh : h 1 = (1 - t : ℂ))
    (hsum : ∀ a, g a + h a = f (q a)) :
    ∀ a, g a = (t : ℂ) * f (q a) := by
  obtain ⟨g', h', heG, heH, he⟩ := positive_summands_descend q hq f g h hsum
  have hG : g' 1 = (t : ℂ) := by
    simpa only [map_one, hg] using heG 1
  have hH : h' 1 = (1 - t : ℂ) := by
    simpa only [map_one, hh] using heH 1
  have hs := PureStateExcision.extreme_positive_summand
    (PureStateExcision.ofPositiveState f hf) hp g' h' ht ht1 hG hH
    (fun b => by
      simpa only [PureStateExcision.toPositiveState_ofPositiveState] using he b)
  intro a
  rw [← heG a]
  simpa only [PureStateExcision.toPositiveState_ofPositiveState] using hs (q a)

/-- Pullback through a quotient preserves purity. -/
theorem exists_pure_state_pullback (q : A →⋆ₐ[ℂ] B) (hq : Function.Surjective q)
    (f : B →ₚ[ℂ] ℂ) (hf : f 1 = 1)
    (hp : PureStateExcision.ofPositiveState f hf ∈
      (PureStateExcision.realStateCarrier (A := B)).extremePoints ℝ) :
    ∃ (F : A →ₚ[ℂ] ℂ) (hF : F 1 = 1),
      PureStateExcision.ofPositiveState F hF ∈
        (PureStateExcision.realStateCarrier (A := A)).extremePoints ℝ ∧
      ∀ a, F a = f (q a) := by
  let F : A →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀ (f.toLinearMap.comp q.toLinearMap)
    (fun a ha => f.map_nonneg (map_nonneg q ha))
  have hF : F 1 = 1 := by change f (q 1) = 1; rw [map_one, hf]
  refine ⟨F, hF, ?_, fun _ => rfl⟩
  apply mem_extremePoints_iff_left.mpr
  refine ⟨PureStateExcision.ofPositiveState_mem F hF, ?_⟩
  intro ξ hξ η hη hseg
  obtain ⟨r, s, hr, hs, hrs, heq⟩ := hseg
  let g := PureStateExcision.toPositiveState ξ hξ
  let h := PureStateExcision.toPositiveState η hη
  let G : A →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀ ((r : ℂ) • g.toLinearMap)
    (fun a ha => mul_nonneg (by exact_mod_cast hr.le) (g.map_nonneg ha))
  let H : A →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀ ((s : ℂ) • h.toLinearMap)
    (fun a ha => mul_nonneg (by exact_mod_cast hs.le) (h.map_nonneg ha))
  let S : A →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀ (G.toLinearMap + H.toLinearMap)
    (fun a ha => add_nonneg (G.map_nonneg ha) (H.map_nonneg ha))
  have hSF : S = F := by
    apply PureStateExcision.positive_state_eq
    intro a
    have hv := congrArg (fun t : WeakDual ℝ (selfAdjoint A) => t a) heq
    change r * ξ a + s * η a = (F a).re at hv
    change (((r : ℂ) * g a + (s : ℂ) * h a).re) = (F a).re
    simp only [g, h, PureStateExcision.toPositiveState_apply, Complex.add_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact hv
  have hG : G 1 = (r : ℂ) := by
    change (r : ℂ) * g 1 = _
    rw [PureStateExcision.toPositiveState_one, mul_one]
  have hsval : s = 1 - r := by linarith
  have hH : H 1 = (1 - r : ℂ) := by
    change (s : ℂ) * h 1 = _
    rw [PureStateExcision.toPositiveState_one, mul_one, hsval]
    simp only [Complex.ofReal_sub, Complex.ofReal_one]
  have hsum (a : A) : G a + H a = f (q a) := congrArg (fun t : A →ₚ[ℂ] ℂ => t a) hSF
  have hscale := pure_pullback_positive_summand q hq f hf hp G H hr
    (by linarith) hG hH hsum
  have hg (a : A) : g a = F a := by
    apply mul_left_cancel₀ (show (r : ℂ) ≠ 0 by exact_mod_cast hr.ne')
    exact hscale a
  apply DFunLike.ext
  intro a
  have hv := congrArg Complex.re (hg a)
  change ξ a = (F a).re
  simpa only [g, PureStateExcision.toPositiveState_apply, Complex.ofReal_re] using hv

end WeakPureInfiniteness

end

end OAI
