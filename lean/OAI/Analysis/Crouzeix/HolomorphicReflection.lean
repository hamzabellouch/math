import Mathlib
import OAI.Analysis.Crouzeix.ReflectionDerivative

namespace OAI

/-! Holomorphic Reflection. -/

noncomputable section

open Set Filter Metric Topology Function Complex InnerProductSpace Real

open scoped Classical ComplexConjugate

namespace CrouzeixHilbert.Conformal

theorem holomorphic_reflection {R : ℝ} (hR : 0 < R) {u : ℂ → ℝ} {f : ℂ → ℂ}
    (hu : HarmonicOnNhd u (upperHalfBall R))
    (huc : ContinuousOn u (closedUpperHalfBall R))
    (hzero : ∀ z ∈ closedBall (0 : ℂ) R, z.im = 0 → u z = 0)
    (hneg : ∀ z ∈ sphere (0 : ℂ) R, 0 < z.im → u z < 0)
    (hf : DifferentiableOn ℂ f (upperHalfBall R))
    (hfn : ∀ z ∈ upperHalfBall R, f z ≠ 0)
    (hlog : EqOn (fun z => Real.log ‖f z‖) u (upperHalfBall R)) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (ball 0 R) ∧
      EqOn g f (upperHalfBall R) ∧ deriv g 0 ≠ 0 ∧
      (∀ z ∈ ball (0 : ℂ) R, z.im = 0 → ‖g z‖ = 1) := by
  let H := schwarzExtension R (oddReflection u)
  have hbound := continuousOn_oddReflection huc hzero
  have hHa : AnalyticOnNhd ℂ H (ball 0 R) := analyticOnNhd_schwarzExtension hR.le hbound
  have hHe : EqOn (fun z => (H z).re) u (upperHalfBall R) := by
    intro z hz
    exact (schwarzExtension_re (ContinuousOn.circleIntegrable hR.le hbound) hz.1).trans
      ((harmonic_reflection hR hu huc hzero).2.1 hz)
  let q : ℂ → ℂ := fun z => f z / Complex.exp (H z)
  have hqd : DifferentiableOn ℂ q (upperHalfBall R) := by
    apply hf.div
    · intro z hz
      exact ((hHa z hz.1).cexp.differentiableAt).differentiableWithinAt
    · exact fun z _ => Complex.exp_ne_zero (H z)
  have hqn : ∀ z ∈ upperHalfBall R, ‖q z‖ = 1 := by
    intro z hz
    dsimp [q]
    rw [norm_div, Complex.norm_exp, show (H z).re = u z from hHe hz, ← (show Real.log ‖f z‖ = u z from hlog hz),
      Real.exp_log (norm_pos_iff.mpr (hfn z hz)), div_self (norm_ne_zero_iff.mpr (hfn z hz))]
  let p : ℂ := (R / 2 : ℝ) * I
  have hp : p ∈ upperHalfBall R := by
    constructor
    · simp only [p, mem_ball_zero_iff, norm_mul, norm_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg (half_pos hR).le]
      linarith
    · change 0 < p.im
      simpa [p] using half_pos hR
  have hqc : EqOn q (fun _ => q p) (upperHalfBall R) :=
    Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (convex_upperHalfBall R).isPreconnected
      (isOpen_upperHalfBall R) hqd hp (fun z hz => by
        change ‖q z‖ ≤ ‖q p‖
        rw [hqn z hz, hqn p hp])
  have hqpn : q p ≠ 0 := by
    intro he
    simpa only [he, norm_zero, zero_ne_one] using hqn p hp
  refine ⟨fun z => q p * Complex.exp (H z), ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact analyticAt_const.mul (hHa z hz).cexp
  · intro z hz
    have he := (div_eq_iff (Complex.exp_ne_zero (H z))).mp (hqc hz)
    exact he.symm
  · have hd := ((hHa 0 (mem_ball_self hR)).differentiableAt.hasDerivAt.cexp).const_mul (q p)
    rw [hd.deriv]
    exact mul_ne_zero hqpn (mul_ne_zero (Complex.exp_ne_zero _) (deriv_schwarzExtension_odd_ne_zero hR hbound hneg))
  · intro z hz hi
    have hr : (H z).re = 0 :=
      (schwarzExtension_re (ContinuousOn.circleIntegrable hR.le hbound) hz).trans
        ((harmonic_reflection hR hu huc hzero).2.2 z hz hi)
    rw [norm_mul, hqn p hp, Complex.norm_exp, hr, Real.exp_zero, mul_one]

end CrouzeixHilbert.Conformal

end

end OAI
