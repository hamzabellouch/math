import OAI.NumberTheory.CubicMoment.Transform.MetaplecticWeightedContinuation
import OAI.NumberTheory.CubicMoment.Estimates.MellinNonvanishingTest
import Mathlib.Analysis.Analytic.Uniqueness

namespace OAI

/-! Compatible regular numerators for different Mellin test functions.
Their compatibility follows by analytic continuation of their literal
Dirichlet-series identity in the half-plane of absolute convergence. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace CubicFirstMoment

def metaplecticRegularNumerator (r : Eisenstein) (W : ℝ → ℂ) (s : ℂ) : ℂ :=
  metaplecticWeightedRegular r W s-
    metaplecticCompletedResidue r*dslope (mellin W) (5/6) s

lemma metaplecticRegularNumerator_differentiableOn
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {r : Eisenstein} (hr : primary r) (hsr : Squarefree r)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) :
    DifferentiableOn ℂ (metaplecticRegularNumerator r W) {s : ℂ | 0 < s.re} := by
  have hp : {s : ℂ | 0 < s.re} ∈ 𝓝 (5/6:ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  exact (metaplecticWeightedRegular_differentiableOn hV hr hsr W hW hpos hsm).sub
    (((Complex.differentiableOn_dslope hp).mpr
      (smooth_mellin_entire W hW hpos hsm.continuous).differentiableOn).const_mul _)

lemma metaplecticRegularNumerator_right
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {r : Eisenstein} (hr : primary r) (hsr : Squarefree r)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {s : ℂ} (hs : 1 < s.re) :
    metaplecticRegularNumerator r W s = mellin W s*
      (metaplecticCompletionEuler r s*metaplecticGaussSeries r s-
        metaplecticCompletedResidue r/(s-5/6)) := by
  have hsp : s ≠ (5/6:ℂ) := by
    intro h
    subst s
    norm_num at hs
  have h := metaplecticWeightedRegular_eq hV hr hsr W hW hpos hsm hs
  have he := eq_sub_of_add_eq h.symm
  rw [metaplecticRegularNumerator,he,dslope_of_ne _ hsp,slope,smul_eq_mul]
  simp only [vsub_eq_sub,div_eq_mul_inv]
  ring

theorem metaplecticRegularNumerator_compatible
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {r : Eisenstein} (hr : primary r) (hsr : Squarefree r)
    (W V : ℝ → ℂ) (hW : HasCompactSupport W) (hWp : tsupport W ⊆ Ioi 0)
    (hWs : ContDiff ℝ ∞ W) (hVcompact : HasCompactSupport V) (hVp : tsupport V ⊆ Ioi 0)
    (hVs : ContDiff ℝ ∞ V) {s : ℂ} (hs : 0 < s.re) :
    metaplecticRegularNumerator r W s*mellin V s =
      metaplecticRegularNumerator r V s*mellin W s := by
  have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hNW := metaplecticRegularNumerator_differentiableOn hV hr hsr W hW hWp hWs
  have hNV := metaplecticRegularNumerator_differentiableOn hV hr hsr V hVcompact hVp hVs
  have hMW := smooth_mellin_entire W hW hWp hWs.continuous
  have hMV := smooth_mellin_entire V hVcompact hVp hVs.continuous
  have hglobal := ((hNW.mul hMV.differentiableOn).analyticOnNhd hopen).eqOn_of_preconnected_of_eventuallyEq
    ((hNV.mul hMW.differentiableOn).analyticOnNhd hopen)
    (convex_halfSpace_re_gt 0).isPreconnected (z₀ := (2:ℂ)) (by norm_num)
  apply hglobal ?_ hs
  have hn : {z : ℂ | 1 < z.re} ∈ 𝓝 (2:ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [hn] with z hz
  simp only [Pi.mul_apply]
  rw [metaplecticRegularNumerator_right hV hr hsr W hW hWp hWs hz,
    metaplecticRegularNumerator_right hV hr hsr V hVcompact hVp hVs hz]
  ring

end CubicFirstMoment

end

end OAI
