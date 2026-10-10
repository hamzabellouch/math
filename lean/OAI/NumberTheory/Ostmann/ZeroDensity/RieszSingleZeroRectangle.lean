import OAI.NumberTheory.Ostmann.ZeroDensity.RieszPoleRectangle
import OAI.NumberTheory.Ostmann.Characters.CharacterLogDerivativePole

namespace OAI

/-! # The actual one-zero contribution to a character Riesz rectangle -/

namespace Ostmann

open Complex Filter Set
open scoped Topology Interval

theorem rieszContour_regular_part (χ : PrimitiveComplexCharacter)
    (X : ℝ) (hX : 0 < X) (z : ℂ) (hz : 0 < z.re) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R z ∧
      (fun s => -logDeriv χ.L s * rieszContourWeight X s +
        (analyticOrderNatAt χ.L z : ℂ) * rieszContourWeight X z / (s - z)) =ᶠ[𝓝[≠] z] R := by
  obtain ⟨g, hg, hgne, hsplit⟩ := χ.logDeriv_local_split z
  let W := rieszContourWeight X
  have hW : AnalyticAt ℂ W z := rieszContourWeight_analyticAt X hX z hz
  have hds := rieszWeight_dslope_analytic X hX z hz z hz
  have hlog : AnalyticAt ℂ (logDeriv g) z := hg.deriv.div hg hgne
  let R : ℂ → ℂ := fun s => -(analyticOrderNatAt χ.L z : ℂ) * dslope W z s - logDeriv g s * W s
  refine ⟨R, (analyticAt_const.mul hds).sub (hlog.mul hW), ?_⟩
  filter_upwards [hsplit, self_mem_nhdsWithin] with s hs hsz
  rw [hs]
  dsimp only [R]
  rw [dslope_of_ne W hsz]
  simp only [slope, smul_eq_mul, vsub_eq_sub]
  ring

theorem rieszContour_single_regularization (χ : PrimitiveComplexCharacter)
    (X : ℝ) (hX : 0 < X) (K : Set ℂ) (z : ℂ) (hz : 0 < z.re)
    (hK : ∀ s ∈ K, 0 < s.re) (hzeros : ∀ s ∈ K, χ.L s = 0 → s = z) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F K ∧ ∀ s ≠ z,
      F s = -logDeriv χ.L s * rieszContourWeight X s +
        (analyticOrderNatAt χ.L z : ℂ) * rieszContourWeight X z / (s - z) := by
  classical
  obtain ⟨R, hR, heR⟩ := rieszContour_regular_part χ X hX z hz
  let f : ℂ → ℂ := fun s => -logDeriv χ.L s * rieszContourWeight X s +
    (analyticOrderNatAt χ.L z : ℂ) * rieszContourWeight X z / (s - z)
  let F : ℂ → ℂ := fun s => if s = z then R z else f s
  refine ⟨F, ?_, fun s hs => by simp [F, hs, f]⟩
  intro s hsK
  by_cases hs : s = z
  · subst s
    apply hR.congr
    have he : ∀ᶠ s in 𝓝 z, s ≠ z → f s = R s := by
      simpa only [mem_compl_iff, mem_singleton_iff, f] using (eventually_nhdsWithin_iff.mp heR)
    filter_upwards [he] with s hs
    by_cases hsz : s = z
    · simp [F, hsz]
    · simpa only [F, ite_eq_right hsz] using (hs hsz).symm
  · have hn : χ.L s ≠ 0 := fun he => hs (hzeros s hsK he)
    have hf : AnalyticAt ℂ f s := by
      apply (((χ.L_analytic s).deriv.div (χ.L_analytic s) hn).neg.mul
        (rieszContourWeight_analyticAt X hX s (hK s hsK))).add
      exact analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hs)
    apply hf.congr
    filter_upwards [isOpen_ne.mem_nhds hs] with t ht
    simp [F, ht]

theorem rieszContour_single_zero_rectangle (χ : PrimitiveComplexCharacter)
    (X : ℝ) (hX : 0 < X) (a b c d : ℝ) (z : ℂ)
    (ha : 0 < a) (haz : a < z.re) (hzb : z.re < b) (hcz : c < z.im) (hzd : z.im < d)
    (hzeros : ∀ s ∈ uIcc a b ×ℂ uIcc c d, χ.L s = 0 → s = z) :
    rectangleBoundaryIntegral (fun s => -logDeriv χ.L s * rieszContourWeight X s) a b c d =
      -(2 * (Real.pi : ℂ) * I) *
        ((analyticOrderNatAt χ.L z : ℂ) * rieszContourWeight X z) := by
  let f : ℂ → ℂ := fun s => -logDeriv χ.L s * rieszContourWeight X s
  let v : ℂ := (analyticOrderNatAt χ.L z : ℂ) * rieszContourWeight X z
  let p : ℂ → ℂ := fun s => v * (s - z)⁻¹
  have hpos (s : ℂ) (hs : s ∈ uIcc a b ×ℂ uIcc c d) : 0 < s.re :=
    ha.trans_le ((uIcc_of_le (haz.trans hzb).le) ▸ hs.1).1
  obtain ⟨F, hF, heF⟩ := rieszContour_single_regularization χ X hX
    (uIcc a b ×ℂ uIcc c d) z (ha.trans haz) hpos hzeros
  have hnot (s : ℂ) (hs : s ∈ contourRectangleBoundary a b c d) : s ≠ z :=
    contourBoundary_ne_interior ⟨haz, hzb, hcz, hzd⟩ hs
  have hf : RectangleIntegrable f a b c d := by
    apply rectangleIntegrable_of_continuousOn
    intro s hs
    have hn : χ.L s ≠ 0 := fun he => hnot s hs (hzeros s ⟨hs.1, hs.2.1⟩ he)
    exact ((((χ.L_analytic s).deriv.div (χ.L_analytic s) hn).neg).mul
      (rieszContourWeight_analyticAt X hX s (hpos s ⟨hs.1, hs.2.1⟩))).continuousAt.continuousWithinAt
  have hp : RectangleIntegrable p a b c d :=
    (rectangleIntegrable_sub_inv ⟨haz, hzb, hcz, hzd⟩).const_mul v
  have he : rectangleBoundaryIntegral F a b c d =
      rectangleBoundaryIntegral (fun s => f s + p s) a b c d := by
    apply rectangleBoundaryIntegral_congr
    intro s hs
    simpa only [f, p, v, div_eq_mul_inv] using heF s (hnot s hs)
  have hzero := rectangleBoundaryIntegral_eq_zero hF
  have hpval : rectangleBoundaryIntegral p a b c d = (2 * (Real.pi : ℂ) * I) * v := by
    rw [show p = (fun s => v * (s - z)⁻¹) from rfl, rectangleBoundaryIntegral_const_mul,
      rectangleBoundaryIntegral_sub_inv z a b c d haz hzb hcz hzd]
    ring
  rw [he, rectangleBoundaryIntegral_add hf hp, hpval] at hzero
  change rectangleBoundaryIntegral f a b c d = -(2 * (Real.pi : ℂ) * I) * v
  linear_combination hzero

end Ostmann

end OAI
