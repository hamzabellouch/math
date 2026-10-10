import Mathlib
import OAI.Analysis.AffineBernstein.SmoothPositivePart

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section SmoothCapTest

/-- A smooth convex cap test, quadratic below the fixed transition interval
and identically zero above it. -/
def smoothCapTest (ε b t : ℝ) : ℝ :=
  ∫ s in (-ε)..(b-t), smoothPositivePart ε s

lemma smoothCapTest_hasDeriv (ε b t : ℝ) :
    HasDerivAt (smoothCapTest ε b) (-smoothPositivePart ε (b-t)) t := by
  have hc := (smoothPositivePart_smooth ε).continuous
  have hi : HasDerivAt (fun z : ℝ => ∫ s in (-ε)..z, smoothPositivePart ε s)
      (smoothPositivePart ε (b-t)) (b-t) :=
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
      hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  change HasDerivAt (fun x : ℝ => ∫ s in (-ε)..(b-x), smoothPositivePart ε s) _ t
  simpa only [Function.comp_def,zero_sub,smul_eq_mul,neg_mul,one_mul] using
    hi.scomp t ((hasDerivAt_const t b).sub (hasDerivAt_id t))

lemma smoothCapTest_second (ε b : ℝ) :
    deriv (deriv (smoothCapTest ε b)) = fun t => smoothPositiveSlope ε (b-t) := by
  have he : deriv (smoothCapTest ε b) = fun t => -smoothPositivePart ε (b-t) :=
    funext fun t => (smoothCapTest_hasDeriv ε b t).deriv
  rw [he]
  funext t
  have hd := ((smoothPositivePart_hasDeriv ε (b-t)).comp t
    ((hasDerivAt_const t b).sub (hasDerivAt_id t))).neg
  simpa only [Function.comp_def,Pi.neg_def,zero_sub,mul_neg,mul_one,neg_neg] using hd.deriv

lemma smoothCapTest_smooth (ε b : ℝ) : ContDiff ℝ ∞ (smoothCapTest ε b) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun t => (smoothCapTest_hasDeriv ε b t).differentiableAt,?_⟩
  rw [show deriv (smoothCapTest ε b) = fun t => -smoothPositivePart ε (b-t) from
    funext fun t => (smoothCapTest_hasDeriv ε b t).deriv]
  exact ((smoothPositivePart_smooth ε).comp (contDiff_const.sub contDiff_id)).neg

lemma smoothCapTest_second_nonneg (ε b t : ℝ) :
    0 ≤ deriv (deriv (smoothCapTest ε b)) t := by
  rw [smoothCapTest_second]
  exact Real.smoothTransition.nonneg _

lemma smoothCapTest_second_one {ε : ℝ} (hε : 0 < ε) {b t : ℝ} (ht : t ≤ b-ε) :
    deriv (deriv (smoothCapTest ε b)) t = 1 := by
  rw [smoothCapTest_second]
  exact smoothPositiveSlope_one hε (by linarith)

lemma smoothCapTest_vanish {ε : ℝ} (hε : 0 < ε) {b t : ℝ} (ht : b+ε ≤ t) :
    smoothCapTest ε b t = 0 ∧ deriv (smoothCapTest ε b) t = 0 ∧
      deriv (deriv (smoothCapTest ε b)) t = 0 := by
  have hbt : b-t ≤ -ε := by linarith
  refine ⟨?_,?_,?_⟩
  · unfold smoothCapTest
    calc
      _ = ∫ s in (-ε)..(b-t), (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_ge hbt] at hs
        exact smoothPositivePart_zero hε hs.2
      _ = 0 := by simp
  · rw [(smoothCapTest_hasDeriv ε b t).deriv,smoothPositivePart_zero hε hbt,neg_zero]
  · rw [smoothCapTest_second]
    exact smoothPositiveSlope_zero hε hbt

/-- All lower-order terms of the cap identity are bounded by a single
constant fixed by the level interval, center level, dimension and cutoff.
Thus the test construction requires no solution-dependent constant. -/
lemma smoothCapTest_lower_order_bound (n : ℕ) (ε b a q₀ : ℝ) :
    ∃ C > 0, ∀ t ∈ Set.Icc a (b+ε),
      (n:ℝ)*(t-q₀)*deriv (smoothCapTest ε b) t +
        (n:ℝ)*((n:ℝ)+1)*smoothCapTest ε b t ≤ C := by
  let g := fun t => (n:ℝ)*(t-q₀)*deriv (smoothCapTest ε b) t +
        (n:ℝ)*((n:ℝ)+1)*smoothCapTest ε b t
  have hg : Continuous g := by
    have h1 : ContDiff ℝ ∞ (deriv (smoothCapTest ε b)) := (smoothCapTest_smooth ε b).deriv'
    exact ((continuous_const.mul (continuous_id.sub continuous_const)).mul h1.continuous).add
      (continuous_const.mul (smoothCapTest_smooth ε b).continuous)
  obtain ⟨C,hC⟩ := isCompact_Icc.bddAbove_image hg.continuousOn
  refine ⟨max 1 C,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro t ht
  exact (hC ⟨t,ht,rfl⟩).trans (le_max_right _ _)

end SmoothCapTest

/-- The quantitative supporting-plane inequality for an actual interior ball,
valid in any real normed ambient space. -/
lemma ball_support_lower {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (ell : V →L[ℝ] ℝ) (o p : V) {r : ℝ} (hr : 0 < r)
    (hs : ∀ z ∈ Metric.closedBall o r, 0 ≤ ell (z-p)) :
    r*‖ell‖ ≤ ell (o-p) := by
  have hZ : 0 ≤ ell (o-p) := hs o (by simp [hr.le])
  have hb (z : V) (hz : ‖z‖ ≤ r) : |ell z| ≤ ell (o-p) := by
    have hp := hs (o+z) (by simpa [Metric.mem_closedBall,dist_eq_norm] using hz)
    have hm := hs (o-z) (by simpa [Metric.mem_closedBall,dist_eq_norm] using hz)
    have hep : ell (o+z-p) = ell (o-p)+ell z := by rw [show o+z-p = o-p+z by abel,map_add]
    have hem : ell (o-z-p) = ell (o-p)-ell z := by rw [show o-z-p = (o-p)-z by abel,map_sub]
    rw [hep] at hp
    rw [hem] at hm
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hn : ‖ell‖ ≤ ell (o-p)/r := by
    apply ell.opNorm_le_bound' (div_nonneg hZ hr.le)
    intro z hz
    have hpz : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have hs := hb ((r/‖z‖) • z) (by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos hr hpz),div_mul_cancel₀ _ hz])
    rw [map_smul,smul_eq_mul,abs_mul,abs_of_pos (div_pos hr hpz)] at hs
    rw [Real.norm_eq_abs]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hr).2
    rw [div_mul_eq_mul_div] at hs
    have hh := (div_le_iff₀ hpz).1 hs
    nlinarith
  simpa only [mul_comm] using (le_div_iff₀ hr).1 hn

end AffineBernstein
end

end OAI
