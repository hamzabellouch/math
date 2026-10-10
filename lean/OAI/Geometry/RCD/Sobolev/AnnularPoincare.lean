import OAI.Geometry.RCD.Sobolev.DirichletPoincare

namespace OAI

/-! # Scale-correct Dirichlet coercivity from annular volume -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

def annularPoincareConstant (K : ℝ) (n : ℕ) : ℝ :=
  16 * Real.exp (8 * n * Real.sqrt (|K| / (n - 1)))

theorem annularPoincareConstant_pos (K : ℝ) (n : ℕ) :
    0 < annularPoincareConstant K n := by
  unfold annularPoincareConstant
  positivity

/-- Doubling of the volume between r and 2r provides enough zero boundary
outside B(r). The transport estimate then gives one constant for all r<=1. -/
theorem NoncollapsedRCD.annular_dirichlet_poincare {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (p : X) {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hvol : 0 < (hausdorff n X).real (ball p r))
    (hdouble : 2 * (hausdorff n X).real (ball p r) ≤
      (hausdorff n X).real (ball p (2 * r)))
    (f : SobolevSpace.dirichlet (hausdorff n X) hX.quadratic (ball p r)) :
    ‖SobolevSpace.toLp (hausdorff n X) hX.quadratic f.val‖ ^ 2 ≤
      (annularPoincareConstant K n * r ^ 2) * energyForm (hausdorff n X) hX.quadratic f.val f.val := by
  let μ := hausdorff n X
  let Ω := ball p r
  let B := ball p (2 * r) \ Ω
  have hΩfin : μ Ω ≠ ∞ := ne_of_lt (hX.finiteOnBounded Ω isBounded_ball)
  have houterfin : μ (ball p (2 * r)) ≠ ∞ :=
    ne_of_lt (hX.finiteOnBounded (ball p (2 * r)) isBounded_ball)
  have hBfin : μ B ≠ ∞ := measure_ne_top_of_subset sdiff_subset houterfin
  have hΩ0 : μ Ω ≠ 0 := by
    intro hh
    have hz : μ.real Ω = 0 := by simp only [Measure.real, hh, ENNReal.toReal_zero]
    exact (ne_of_gt hvol) hz
  have hVB : μ.real Ω ≤ μ.real B := by
    have he : μ.real B = μ.real (ball p (2 * r)) - μ.real Ω :=
      measureReal_sdiff (ball_subset_ball (by linarith)) measurableSet_ball houterfin
    rw [he]
    linarith
  have hB0 : μ B ≠ 0 := by
    intro hh
    have hz : μ.real B = 0 := by simp only [Measure.real, hh, ENNReal.toReal_zero]
    linarith
  have hmeasure : μ Ω ≤ μ B := by
    rw [← ofReal_measureReal hΩfin, ← ofReal_measureReal hBfin]
    exact ENNReal.ofReal_le_ofReal hVB
  have hmax : max (μ Ω)⁻¹ (μ B)⁻¹ = (μ Ω)⁻¹ :=
    max_eq_left (ENNReal.inv_le_inv.mpr hmeasure)
  let P := μ.real Ω * (4 * r) ^ 2 *
    (compressionBudget K n (4 * r) (max (μ Ω)⁻¹ (μ B)⁻¹)).toReal
  have hPform : P = 16 * r ^ 2 * Real.exp (8 * n * r * Real.sqrt (|K| / (n - 1))) := by
    dsimp only [P]
    rw [hmax, compressionBudget, compressionStep, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.exp_pos _).le, ENNReal.toReal_inv]
    change μ.real Ω * (4 * r) ^ 2 *
      (Real.exp ((n : ℝ) * (2 * (4 * r)) * Real.sqrt (|K| / ((n : ℝ) - 1))) * (μ.real Ω)⁻¹) = _
    have he : (n : ℝ) * (2 * (4 * r)) = 8 * n * r := by ring
    rw [he]
    field_simp [ne_of_gt (show 0 < μ.real Ω from hvol)]
    norm_num
  have hPbound : P ≤ annularPoincareConstant K n * r ^ 2 := by
    rw [hPform]
    have harg : 8 * n * r * Real.sqrt (|K| / ((n : ℝ) - 1)) ≤
        8 * n * Real.sqrt (|K| / ((n : ℝ) - 1)) := by
      calc
        _ = (8 * n * Real.sqrt (|K| / ((n : ℝ) - 1))) * r := by ring
        _ ≤ (8 * n * Real.sqrt (|K| / ((n : ℝ) - 1))) * 1 :=
          mul_le_mul_of_nonneg_left hr1 (by positivity)
        _ = _ := mul_one _
    have hexp := Real.exp_le_exp.mpr harg
    unfold annularPoincareConstant
    nlinarith [sq_nonneg r]
  let u := SobolevSpace.toLp μ hX.quadratic f.val
  let g := SobolevSpace.minimalSlope μ hX.quadratic f.val
  have hz : u =ᵐ[μ.restrict Ωᶜ] 0 :=
    SobolevSpace.dirichlet_zero_off μ hX.quadratic Ω measurableSet_ball f
  have hzB : u =ᵐ[μ.restrict B] 0 :=
    ae_restrict_of_ae_restrict_of_subset (fun _ hx => hx.2) hz
  have hi := hX.dirichlet_integral_coercivity K n hn p (by linarith : 0 ≤ 2 * r)
    measurableSet_ball (measurableSet_ball.diff measurableSet_ball) hΩ0 hB0
    ((ball_subset_ball (by linarith)).trans ball_subset_closedBall)
    (sdiff_subset.trans ball_subset_closedBall)
    (SobolevSpace.minimalSlope_isRelaxed μ hX.quadratic f.val) hzB
  have hu : (∫ x in Ω, (u x) ^ 2 ∂μ) = ‖u‖ ^ 2 := by
    rw [setIntegral_eq_integral_of_ae_compl_eq_zero, lp_integral_square_eq_norm_square]
    filter_upwards [(ae_restrict_iff' measurableSet_ball.compl).mp hz] with x hx hnot
    simp [hx hnot]
  have hg : (∫ x, (g x) ^ 2 ∂μ) = energyForm μ hX.quadratic f.val f.val := by
    rw [lp_integral_square_eq_norm_square]
    exact (SobolevSpace.minimalSlope_norm_sq μ hX.quadratic f.val).trans
      (energyForm_self μ hX.quadratic f.val).symm
  simp only [show 2 * (2 * r) = 4 * r by ring] at hi
  change (∫ x in Ω, (u x) ^ 2 ∂μ) ≤ P * (∫ x, (g x) ^ 2 ∂μ) at hi
  rw [hu, hg] at hi
  exact hi.trans (mul_le_mul_of_nonneg_right hPbound
    (by rw [← hg]; exact integral_nonneg fun _ => sq_nonneg _))

end RegularPointCoordinates

end

end OAI
