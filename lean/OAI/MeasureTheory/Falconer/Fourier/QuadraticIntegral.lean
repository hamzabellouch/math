import OAI.MeasureTheory.Falconer.Fourier.QuadraticJacobian
import OAI.MeasureTheory.Falconer.Angular.PublishedGnomonic

namespace OAI

/-!
# The actual sphere integral in fixed quadratic coordinates

The only measure input is the already recorded gnomonic surface formula.
The quadratic coordinate Jacobian is proved locally. Its product with the
gnomonic density is exactly the manuscript's `(1-‖u‖²/4)^((n-2)/2)`.
-/

namespace Falconer
open Set MeasureTheory

theorem quadratic_gnomonic_density {n : ℕ} {u : Space n} (hu : ‖u‖ < 1) :
    gnomonicDensity (quadraticToGnomonic u) = (1-‖u‖^2/2)^(n+1) := by
  let a : ℝ := 1-‖u‖^2/2
  have hu2 : ‖u‖^2 < 1 := by
    simpa using (sq_lt_sq₀ (norm_nonneg u) (by norm_num : (0:ℝ) ≤ 1)).mpr hu
  have ha : 0 < a := by dsimp [a]; linarith
  have hp := congrArg (fun x : Space (n+1) => x 0)
    (gnomonicChart_quadraticToGnomonic hu)
  simp only [gnomonicChart_zero, quadraticSpherePoint_zero_coord] at hp
  have hn : ‖northLift (quadraticToGnomonic u)‖ = a⁻¹ := by
    have hi := congrArg Inv.inv hp
    simpa only [inv_inv] using hi
  unfold gnomonicDensity
  rw [← northLift_norm_sq, hn]
  change ((a⁻¹)^2)^(-((n+1 : ℕ) : ℝ)/2) = a^(n+1)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (inv_nonneg.mpr ha.le),
    Real.inv_rpow ha.le, ← Real.rpow_neg ha.le]
  convert Real.rpow_natCast a (n+1) using 1
  congr 1
  push_cast
  ring

theorem quadratic_jacobian_density (m : ℕ) {u : Space (m+2)} (hu : ‖u‖ < 1) :
    |(quadraticCoordinateDifferential u).det| *
      gnomonicDensity (quadraticToGnomonic u) = (Real.sqrt (1-‖u‖^2/4))^m := by
  rw [abs_of_pos (quadraticCoordinateDifferential_det_pos m hu),
    quadraticCoordinateDifferential_det_explicit m hu, quadratic_gnomonic_density hu]
  have hu2 : ‖u‖^2 < 1 := by
    simpa using (sq_lt_sq₀ (norm_nonneg u) (by norm_num : (0:ℝ) ≤ 1)).mpr hu
  have ha : 1-‖u‖^2/2 ≠ 0 := by linarith
  have hn : (m+2)+1 = m+3 := by omega
  rw [hn, div_mul_cancel₀ _ (pow_ne_zero _ ha)]

/-- A function supported in this fixed north-pole chart has exactly the
quadratic-coordinate integral, including its surface Jacobian. -/
theorem quadratic_sphere_integral (hpublished : PublishedGnomonicSurface)
    (m : ℕ) (f : Sphere (m+3) → ℂ) (hf : Measurable f)
    (hs : ∀ w, w ∉ northHemisphere (m+2) → f w = 0)
    (hchart : ∀ x : Space (m+2),
      x ∉ quadraticToGnomonic '' Metric.ball (0 : Space (m+2)) 1 →
        f (gnomonicChart x) = 0) :
    (∫ w, f w ∂sphereMeasure (m+3)) =
      ∫ u in Metric.ball (0 : Space (m+2)) 1,
        (Real.sqrt (1-‖u‖^2/4))^m • f (gnomonicChart (quadraticToGnomonic u)) := by
  rw [gnomonic_sphere_integral hpublished (by omega) f hf hs]
  let U := Metric.ball (0 : Space (m+2)) 1
  let g : Space (m+2) → ℂ := fun x => gnomonicDensity x • f (gnomonicChart x)
  have hg : ∀ x, x ∉ quadraticToGnomonic '' U → g x = 0 := by
    intro x hx
    simp only [g, hchart x hx, smul_zero]
  change (∫ x, g x) = _
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hg]
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume measurableSet_ball
    (fun u hu => (quadraticToGnomonic_hasFDerivAt (by
      simpa only [U, Metric.mem_ball, dist_zero_right] using hu)).hasFDerivWithinAt)
    (quadraticToGnomonic_injOn (m+2)) g]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (show MeasurableSet U from measurableSet_ball)] with u hu
  have hu' : ‖u‖ < 1 := by simpa only [U, Metric.mem_ball, dist_zero_right] using hu
  simp only [g, smul_smul, quadratic_jacobian_density m hu']

/-- The north-pole phase is exactly a constant phase times the negative
quadratic phase. This is the local integral to which quadratic stationary
phase will be applied. -/
theorem quadratic_sphere_oscillatory_integral (hpublished : PublishedGnomonicSurface)
    (m : ℕ) (Λ : ℝ) (b : Sphere (m+3) → ℂ) (hb : Measurable b)
    (hs : ∀ w, w ∉ northHemisphere (m+2) → b w = 0)
    (hchart : ∀ x : Space (m+2),
      x ∉ quadraticToGnomonic '' Metric.ball (0 : Space (m+2)) 1 →
        b (gnomonicChart x) = 0) :
    (∫ w : Sphere (m+3),
      Complex.exp (Complex.I*(Λ : ℂ)*
        (inner ℝ (w : Space (m+3)) (coordinateJoin (0 : Space (m+2)) 1) : ℂ)) * b w
      ∂sphereMeasure (m+3)) =
    Complex.exp (Complex.I*(Λ : ℂ)) *
      ∫ u in Metric.ball (0 : Space (m+2)) 1,
        Complex.exp (-(Complex.I*(Λ : ℂ)/2)*(‖u‖^2 : ℝ)) *
          ((Real.sqrt (1-‖u‖^2/4))^m : ℂ) * b (gnomonicChart (quadraticToGnomonic u)) := by
  let f : Sphere (m+3) → ℂ := fun w =>
    Complex.exp (Complex.I*(Λ : ℂ)*
      (inner ℝ (w : Space (m+3)) (coordinateJoin (0 : Space (m+2)) 1) : ℂ)) * b w
  have hf : Measurable f := by
    apply Measurable.mul _ hb
    fun_prop
  have hfs : ∀ w, w ∉ northHemisphere (m+2) → f w = 0 := by
    intro w hw
    simp only [f, hs w hw, mul_zero]
  have hfc : ∀ x : Space (m+2),
      x ∉ quadraticToGnomonic '' Metric.ball (0 : Space (m+2)) 1 →
        f (gnomonicChart x) = 0 := by
    intro x hx
    simp only [f, hchart x hx, mul_zero]
  change (∫ w, f w ∂sphereMeasure (m+3)) = _
  rw [quadratic_sphere_integral hpublished m f hf hfs hfc, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_ball :
    MeasurableSet (Metric.ball (0 : Space (m+2)) 1))] with u hu
  have hu' : ‖u‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hu
  have hp : inner ℝ (gnomonicChart (quadraticToGnomonic u) : Space (m+3))
      (coordinateJoin (0 : Space (m+2)) 1) = 1-‖u‖^2/2 := by
    rw [gnomonicChart_quadraticToGnomonic hu', quadraticSpherePoint_phase]
  have he : Complex.I*(Λ : ℂ)*((1-‖u‖^2/2 : ℝ) : ℂ) =
      Complex.I*(Λ : ℂ) + -(Complex.I*(Λ : ℂ)/2)*(‖u‖^2 : ℝ) := by
    push_cast
    ring
  simp only [f, hp, he, Complex.exp_add, Complex.real_smul, Complex.ofReal_pow]
  ring

end Falconer

end OAI
