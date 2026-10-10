import OAI.Geometry.RCD.Sobolev.LocalZeroSetCoercivity
import OAI.Geometry.RCD.Sobolev.DirichletPoincare

namespace OAI

/-! # Uniform Dirichlet coercivity from an exterior annulus -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.uniform_annular_coercivity {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) :
    ∃ P : ℝ, 0 < P ∧ ∀ (p : X) (r : ℝ), 0 < r → -1 ≤ K*(2*r)^2 →
      2*(hausdorff n X).real (ball p r) ≤ (hausdorff n X).real (ball p (2*r)) →
      ∀ w : SobolevSpace.dirichlet (hausdorff n X) hX.quadratic (ball p r),
        ‖SobolevSpace.toLp (hausdorff n X) hX.quadratic w.val‖^2 ≤
          P*r^2 * energyForm (hausdorff n X) hX.quadratic w.val w.val := by
  obtain ⟨C, hC, hlocal⟩ := hX.local_zero_set_coercivity hn (by norm_num : (0:ℝ)≤1)
  refine ⟨4*C, by positivity, ?_⟩
  intro p r hr hcurv hvol w
  let μ := hausdorff n X
  let u := SobolevSpace.toLp μ hX.quadratic w.val
  let G := SobolevSpace.minimalSlope μ hX.quadratic w.val
  let B := ball p (2*r) \ ball p r
  have hz := SobolevSpace.dirichlet_zero_off μ hX.quadratic (ball p r) measurableSet_ball w
  have hBhalf : μ.real (ball p (2*r)) ≤ 2*μ.real B := by
    have he : μ.real B = μ.real (ball p (2*r)) - μ.real (ball p r) :=
      measureReal_sdiff (μ := μ) (ball_subset_ball (by linarith : r≤2*r))
        measurableSet_ball (hX.finiteOnBounded _ isBounded_ball).ne
    change 2*μ.real (ball p r) ≤ μ.real (ball p (2*r)) at hvol
    linarith
  have hzB : u =ᵐ[μ.restrict B] 0 := ae_restrict_of_ae_restrict_of_subset
    (fun _ hx => hx.2) hz
  have hh := hlocal p (2*r) (by positivity) hcurv w.val B
    (measurableSet_ball.diff measurableSet_ball) sdiff_subset hBhalf hzB
  have hu : (∫ x in ball p (2*r), u x^2 ∂μ) = ‖u‖^2 := by
    rw [setIntegral_eq_integral_of_ae_compl_eq_zero, lp_integral_square_eq_norm_square]
    have hzout : u =ᵐ[μ.restrict (ball p (2*r))ᶜ] 0 :=
      ae_restrict_of_ae_restrict_of_subset
        (compl_subset_compl.mpr (ball_subset_ball (by linarith : r≤2*r))) hz
    filter_upwards [(ae_restrict_iff' measurableSet_ball.compl).mp hzout] with x hx hnot
    simp [hx hnot]
  have he : (∫ x in ball p (8*(2*r)), localGamma μ hX.quadratic w.val w.val x ∂μ) ≤
      energyForm μ hX.quadratic w.val w.val := by
    rw [integral_congr_ae (ae_restrict_of_ae (localGamma_self μ hX.quadratic w.val))]
    calc
      _ ≤ ∫ x, G x^2 ∂μ := setIntegral_le_integral (Lp.memLp G).integrable_sq
        (Filter.Eventually.of_forall (fun x => sq_nonneg (G x)))
      _ = _ := by
        rw [lp_integral_square_eq_norm_square]
        exact (SobolevSpace.minimalSlope_norm_sq μ hX.quadratic w.val).trans
          (energyForm_self μ hX.quadratic w.val).symm
  rw [hu] at hh
  calc
    _ ≤ C*(2*r)^2 * ∫ x in ball p (8*(2*r)),
        localGamma μ hX.quadratic w.val w.val x ∂μ := hh
    _ ≤ C*(2*r)^2 * energyForm μ hX.quadratic w.val w.val :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by ring

end RegularPointCoordinates

end

end OAI
