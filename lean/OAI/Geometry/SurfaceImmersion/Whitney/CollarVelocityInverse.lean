import OAI.Geometry.SurfaceImmersion.Whitney.CollarVelocityClock

namespace OAI

/-! Smooth parameter dependence of the explicit collar clock's inverse. -/
noncomputable section
open Filter
open scoped Topology ContDiff

namespace ClosedSurfaceR4.CollarVelocity

lemma clock_smooth : ContDiff ℝ ∞ (fun z : ℝ × ℝ => clock z.1 z.2) := by
  apply contDiff_snd.add
  apply ContDiff.mul
  · exact (contDiff_fst.pow 2).div
      (contDiff_const.mul (contDiff_const.add (contDiff_fst.pow 2)))
      (fun z => by positivity)
  · exact (contDiff_const.mul contDiff_snd).sin

def inverseClock (a θ : ℝ) : ℝ := Function.invFun (clock a) θ

@[simp] lemma clock_inverseClock (a θ : ℝ) : clock a (inverseClock a θ) = θ :=
  Function.rightInverse_invFun (clock_surjective a) θ

@[simp] lemma inverseClock_clock (a t : ℝ) : inverseClock a (clock a t) = t :=
  Function.leftInverse_invFun (clock_strictMono a).injective t

@[simp] lemma clock_zero (a : ℝ) : clock a 0 = 0 := by simp [clock]
@[simp] lemma inverseClock_zero (a : ℝ) : inverseClock a 0 = 0 := by
  simpa only [clock_zero] using inverseClock_clock a 0

lemma inverseClock_period (a θ : ℝ) :
    inverseClock a (θ + 2 * Real.pi) = inverseClock a θ + 2 * Real.pi := by
  apply (clock_strictMono a).injective
  rw [clock_inverseClock, clock_period, clock_inverseClock]

private def equation (z : (ℝ × ℝ) × ℝ) : ℝ := clock z.1.1 z.2 - z.1.2

private lemma equation_smooth : ContDiff ℝ ∞ equation := by
  exact (clock_smooth.comp (contDiff_fst.fst.prodMk contDiff_snd)).sub contDiff_fst.snd

private lemma equation_partial (a θ t : ℝ) :
    fderiv ℝ equation ((a, θ), t) ∘L ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ =
      ContinuousLinearMap.toSpanSingleton ℝ (density a t) := by
  have he := equation_smooth.differentiable (by norm_num)
  have hi : HasFDerivAt (fun s : ℝ => ((a, θ), s))
      (ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ) t := by
    exact hasFDerivAt_prodMk_right (a, θ) t
  have hcomp := he.differentiableAt.hasFDerivAt.comp t hi
  have hderiv := ((hasDerivAt_clock a t).sub_const θ).hasFDerivAt
  exact hcomp.unique hderiv

private lemma equation_partial_invertible (a θ t : ℝ) :
    (fderiv ℝ equation ((a, θ), t) ∘L ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ).IsInvertible := by
  rw [equation_partial]
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := ContinuousLinearMap.toSpanSingleton ℝ (density a t)⁻¹)
  · ext
    simp [ContinuousLinearMap.toSpanSingleton_apply, (density_pos a t).ne']
  · ext
    simp [ContinuousLinearMap.toSpanSingleton_apply, (density_pos a t).ne']

lemma inverseClock_smooth : ContDiff ℝ ∞ (fun z : ℝ × ℝ => inverseClock z.1 z.2) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  let u : (ℝ × ℝ) × ℝ := (z, inverseClock z.1 z.2)
  have hc := equation_smooth.contDiffAt (x := u)
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have hi := equation_partial_invertible z.1 z.2 (inverseClock z.1 z.2)
  have hs := hc.contDiffAt_implicitFunction hn hi
  have he := hc.eventually_apply_implicitFunction hn hi
  have heq : (fun w : ℝ × ℝ => inverseClock w.1 w.2) =ᶠ[𝓝 z]
      hc.implicitFunction hn hi := by
    filter_upwards [he] with w hw
    apply (clock_strictMono w.1).injective
    rw [clock_inverseClock]
    change clock w.1 (hc.implicitFunction hn hi w) - w.2 =
      clock z.1 (inverseClock z.1 z.2) - z.2 at hw
    rw [clock_inverseClock, sub_self] at hw
    exact (sub_eq_zero.mp hw).symm
  exact hs.congr_of_eventuallyEq heq

end ClosedSurfaceR4.CollarVelocity

end

end OAI
