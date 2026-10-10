import OAI.Geometry.RCD.Harmonic.SignedRadialWeight
import OAI.Geometry.RCD.Heat.HeatMassSmoothing
import OAI.Geometry.RCD.Heat.HeatKernelRows

namespace OAI

/-! # Weighted point evaluations of the actual heat semigroup

The local parabolic estimate and the signed Davies weight retain the sharp
quadratic cost in the exponent. No Gaussian bound is used.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X]

theorem radialWeight_ball_lower (q x : X) (a R r : ℝ) {y : X}
    (hy : y ∈ ball x r) :
    Real.exp (a*min (dist q x) R-|a| *r) ≤ radialWeight q a R y := by
  have hl := ((LipschitzWith.dist_right q).min_const R).dist_le_mul x y
  simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hl
  have hdist : dist x y < r := by simpa only [dist_comm] using mem_ball.mp hy
  have hmul : a*(min (dist q x) R-min (dist q y) R) ≤ |a| *r := calc
    _ ≤ |a*(min (dist q x) R-min (dist q y) R)| := le_abs_self _
    _ = |a| *|min (dist q x) R-min (dist q y) R| := abs_mul _ _
    _ ≤ |a| *r := mul_le_mul_of_nonneg_left (hl.trans hdist.le) (abs_nonneg a)
  apply Real.exp_le_exp.mpr
  nlinarith only [hmul]

variable [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

theorem heatAt_ball_weighted_square_bound (f : Lp ℝ 2 μ) (q x : X)
    (a : ℝ) {R r s t : ℝ} (hR : 0 ≤ R) (hs : 0 ≤ s) (hst : s ≤ t) :
    (∫ y in ball x r, (heatAt μ hQ s f y)^2 ∂μ) ≤
      Real.exp (-a*min (dist q x) R+|a| *r+a^2/2*t)*
        (∫ y, radialWeight q a R y*(f y)^2 ∂μ) := by
  let u := heatAt μ hQ s f
  let b := Real.exp (a*min (dist q x) R-|a| *r)
  have hi := heatAt_signed_radialWeight_integral μ hQ f q a hR hs
  have hw : b*(∫ y in ball x r, (u y)^2 ∂μ) ≤
      ∫ y in ball x r, radialWeight q a R y*(u y)^2 ∂μ := by
    rw [← integral_const_mul]
    apply setIntegral_mono_on ((Lp.memLp u).integrable_sq.const_mul b).integrableOn
      hi.1.integrableOn measurableSet_ball
    intro y hy
    exact mul_le_mul_of_nonneg_right (radialWeight_ball_lower q x a R r hy) (sq_nonneg _)
  have htint : (∫ y, radialWeight q a R y*(f y)^2 ∂μ) ≥ 0 :=
    integral_nonneg fun y => mul_nonneg (radialWeight_nonneg q a R y) (sq_nonneg _)
  have hbound : b*(∫ y in ball x r, (u y)^2 ∂μ) ≤
      Real.exp (a^2/2*t)*(∫ y, radialWeight q a R y*(f y)^2 ∂μ) :=
    hw.trans ((setIntegral_le_integral hi.1
      (Eventually.of_forall fun y => mul_nonneg (radialWeight_nonneg q a R y) (sq_nonneg _))).trans
        (hi.2.trans (mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hst (by positivity))) htint)))
  apply (mul_le_mul_iff_right₀ (Real.exp_pos (a*min (dist q x) R-|a| *r))).mp
  change b*(∫ y in ball x r, (u y)^2 ∂μ) ≤ _
  calc
    _ ≤ Real.exp (a^2/2*t)*(∫ y, radialWeight q a R y*(f y)^2 ∂μ) := hbound
    _ = _ := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring

namespace NoncollapsedRCD

variable {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
  [IsLocallyFiniteMeasure (hausdorff n X)]

include hn in
/-- Weighted point evaluation, for any continuous heat representative.
The positive parameter `M` bounds the weighted initial L² norm. -/
theorem heat_weighted_evaluation :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (q x : X) (a R r t M : ℝ),
      0 ≤ R → 0 < r → -1 ≤ K*r^2 → r^2 < t → 0 < M →
      ∀ (f : Lp ℝ 2 (hausdorff n X)) (v : X → ℝ), Continuous v →
      (v =ᵐ[hausdorff n X] heatAt (hausdorff n X) hX.quadratic t f) →
      (∫ y, radialWeight q a R y*(f y)^2 ∂hausdorff n X) ≤ M^2 →
      |v x| ≤ C/Real.sqrt ((hausdorff n X).real (ball x r))*
        (Real.exp ((-a*min (dist q x) R+|a| *r)/2+a^2/4*t)*M) := by
  obtain ⟨C,hC,hbound⟩ := hX.heat_cylinder_L2_smoothing hn
  refine ⟨C,hC,?_⟩
  intro q x a R r t M hR hr hcurv hrt hM f v hv hrep hnorm
  let μ := hausdorff n X
  let E := Real.exp ((-a*min (dist q x) R+|a| *r)/2+a^2/4*t)
  have hE : 0 < E := Real.exp_pos _
  have hEsq : E^2 = Real.exp (-a*min (dist q x) R+|a| *r+a^2/2*t) := by
    dsimp only [E]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hc := continuous_setIntegral_sq_path μ (heatAt_continuous μ hX.quadratic f)
    (S := ball x r) measurableSet_ball
  have hpoint (s : ℝ) (hs : s ∈ Icc (t-r^2) t) :
      (∫ y in ball x r, (heatAt μ hX.quadratic s f y)^2 ∂μ) ≤ (E*M)^2 := by
    have hspos : 0 ≤ s := (sub_pos.mpr hrt).le.trans hs.1
    have hh := heatAt_ball_weighted_square_bound μ hX.quadratic f q x a hR hspos hs.2
      (r := r)
    rw [← hEsq] at hh
    exact hh.trans (by simpa only [mul_pow] using
      mul_le_mul_of_nonneg_left hnorm (sq_nonneg E))
  have hmass : (∫ s in (t-r^2)..t, ∫ y in ball x r,
      (heatAt μ hX.quadratic s f y)^2 ∂μ) ≤ r^2*(E*M)^2 := by
    have hh := intervalIntegral.integral_mono_on (by linarith [sq_nonneg r] : t-r^2 ≤ t)
      (hc.intervalIntegrable (μ := volume) _ _)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (E*M)^2) volume (t-r^2) t)
      hpoint
    simpa only [intervalIntegral.integral_const,smul_eq_mul,sub_sub_cancel] using hh
  have ha := hbound x r (t-r^2) (E*M) hr hcurv (sub_pos.mpr hrt) (mul_pos hE hM) f
  rw [show t-r^2+r^2 = t by ring] at ha
  have hae := ha hmass
  let := hX.openPos K n
  have hmin : (fun y => min |v y| (C/Real.sqrt (μ.real (ball x r))*(E*M)))
      =ᵐ[μ.restrict (ball x (r/2))] (fun y => |v y|) := by
    filter_upwards [hae,ae_restrict_of_ae hrep] with y hy he
    exact min_eq_left (by simpa only [← he] using hy)
  have heq := Measure.eqOn_open_of_ae_eq hmin isOpen_ball
    (hv.abs.min continuous_const).continuousOn hv.abs.continuousOn
  exact min_eq_left_iff.mp (heq (mem_ball_self (half_pos hr)))

end NoncollapsedRCD
end RegularPointCoordinates

end

end OAI
