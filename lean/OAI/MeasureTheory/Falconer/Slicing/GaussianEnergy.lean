import OAI.MeasureTheory.Falconer.Slicing.GaussianMass

namespace OAI

/-! # The all-dimensional Gaussian Fourier energy bound -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal RealInnerProductSpace

variable {d : ℕ}

theorem gaussian_mass_bound_real (μ : Measure (Space d)) {B K s : ℝ} {k : ℕ}
    (hB : 0 < B) (hK : 0 ≤ K) (hsk : s ≤ k)
    (hb : ∀ x : Space d, ∀ r : ℝ, 1/B ≤ r →
      μ (ball x r) ≤ ENNReal.ofReal (K*r^s)) (x : Space d) :
    (∫ y, Real.exp (-(B*dist x y)^2) ∂μ) ≤ K*(1/B)^s*gaussianBallConstant k := by
  rw [integral_eq_lintegral_of_nonneg_ae (by filter_upwards with y; positivity)
    (by fun_prop)]
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (gaussian_mass_bound μ hB hK hsk hb x)
  rwa [ENNReal.toReal_ofReal (mul_nonneg (mul_nonneg hK (by positivity))
    (gaussianBallConstant_nonneg k))] at h

theorem gaussian_energy_bound (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {B K s : ℝ} {k : ℕ} (hB : 0 < B) (hK : 0 ≤ K) (hsk : s ≤ k)
    (hb : ∀ x : Space d, ∀ r : ℝ, 1/B ≤ r →
      μ (ball x r) ≤ ENNReal.ofReal (K*r^s)) :
    (∫ x, ∫ y, Real.exp (-(B*dist x y)^2) ∂μ ∂μ) ≤
      μ.real univ*(K*(1/B)^s*gaussianBallConstant k) := by
  have hi : Integrable (fun z : Space d × Space d =>
      Real.exp (-(B*dist z.1 z.2)^2)) (μ.prod μ) := by
    apply (integrable_const (1:ℝ)).mono (by fun_prop)
    filter_upwards with z
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),norm_one]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))
  calc
    _ ≤ ∫ _ : Space d, K*(1/B)^s*gaussianBallConstant k ∂μ :=
      integral_mono hi.integral_prod_left (integrable_const _)
        (gaussian_mass_bound_real μ hB hK hsk hb)
    _ = _ := by rw [integral_const,smul_eq_mul]

theorem fourier_gaussian_energy_bound (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {B K s : ℝ} {k : ℕ} (hB : 0 < B) (hK : 0 ≤ K) (hsk : s ≤ k)
    (hb : ∀ x : Space d, ∀ r : ℝ, 1/B ≤ r →
      μ (ball x r) ≤ ENNReal.ofReal (K*r^s)) :
    (∫ ξ : Space d, Real.exp (-(Real.pi^2/B^2)*‖ξ‖^2)*
      ‖PlanarFalconer.sourceFourier μ ξ‖^2) ≤
      (B^2/Real.pi)^((d:ℝ)/2)*(μ.real univ*(K*(1/B)^s*gaussianBallConstant k)) := by
  have hb' : 0 < Real.pi^2/B^2 := div_pos (sq_pos_of_pos Real.pi_pos) (sq_pos_of_pos hB)
  rw [PlanarFalconer.gaussian_lebesgue_square μ hb']
  have h₁ : Real.pi/(Real.pi^2/B^2) = B^2/Real.pi := by field_simp
  have h₂ : Real.pi^2/(Real.pi^2/B^2) = B^2 := by field_simp
  rw [h₁,h₂]
  have he : (fun x : Space d => ∫ y, Real.exp (-B^2*‖x-y‖^2) ∂μ) =
      fun x => ∫ y, Real.exp (-(B*dist x y)^2) ∂μ := by
    funext x
    apply integral_congr_ae
    filter_upwards with y
    rw [dist_eq_norm]
    congr 1
    ring
  rw [he]
  simpa only [Space,finrank_euclideanSpace_fin] using
    mul_le_mul_of_nonneg_left (gaussian_energy_bound μ hB hK hsk hb)
      (Real.rpow_nonneg (by positivity : 0 ≤ B^2/Real.pi) ((d:ℝ)/2))

/-- A Gaussian majorant of the Fourier energy in a fixed multiple of the frequency ball. -/
theorem fourier_ball_energy_bound (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {B K s C : ℝ} {k : ℕ} (hB : 0 < B) (hK : 0 ≤ K) (hsk : s ≤ k) (hC : 0 ≤ C)
    (hb : ∀ x : Space d, ∀ r : ℝ, 1/B ≤ r →
      μ (ball x r) ≤ ENNReal.ofReal (K*r^s)) :
    (∫ ξ in ball (0:Space d) (C*B), ‖PlanarFalconer.sourceFourier μ ξ‖^2) ≤
      Real.exp (Real.pi^2*C^2)*(B^2/Real.pi)^((d:ℝ)/2)*
        (μ.real univ*(K*(1/B)^s*gaussianBallConstant k)) := by
  let f : Space d → ℝ := fun ξ => ‖PlanarFalconer.sourceFourier μ ξ‖^2
  let G : Space d → ℝ := fun ξ => Real.exp (-(Real.pi^2/B^2)*‖ξ‖^2)*f ξ
  have hb' : 0 < Real.pi^2/B^2 := by positivity
  have hG : Integrable G := PlanarFalconer.gaussian_sourceFourier_integrable μ hb'
  have hf : Continuous f := by unfold f PlanarFalconer.sourceFourier; fun_prop
  have hfi : IntegrableOn f (ball (0:Space d) (C*B)) :=
    (hf.continuousOn.integrableOn_compact (isCompact_closedBall (0:Space d) (C*B))).mono_set
      ball_subset_closedBall
  have hpt : ∀ ξ ∈ ball (0:Space d) (C*B), f ξ ≤ Real.exp (Real.pi^2*C^2)*G ξ := by
    intro ξ hξ
    have hn : ‖ξ‖ ≤ C*B := (show ‖ξ‖ < C*B by simpa only [mem_ball,dist_zero_right] using hξ).le
    have hx : 0 ≤ Real.pi^2*C^2-(Real.pi^2/B^2)*‖ξ‖^2 := by
      have hs : ‖ξ‖^2 ≤ (C*B)^2 := sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC hB.le) |>.mpr hn
      have hb2 : 0 < B^2 := sq_pos_of_pos hB
      apply sub_nonneg.mpr
      rw [div_mul_eq_mul_div,div_le_iff₀ hb2]
      nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg Real.pi)]
    have hexp : 1 ≤ Real.exp (Real.pi^2*C^2-(Real.pi^2/B^2)*‖ξ‖^2) :=
      Real.one_le_exp_iff.mpr hx
    calc
      f ξ = 1*f ξ := (one_mul _).symm
      _ ≤ Real.exp (Real.pi^2*C^2-(Real.pi^2/B^2)*‖ξ‖^2)*f ξ :=
        mul_le_mul_of_nonneg_right hexp (sq_nonneg _)
      _ = _ := by dsimp [G]; rw [← mul_assoc,← Real.exp_add]; congr 2; ring
  calc
    _ ≤ ∫ ξ in ball (0:Space d) (C*B), Real.exp (Real.pi^2*C^2)*G ξ :=
      setIntegral_mono_on hfi (hG.const_mul _).integrableOn measurableSet_ball hpt
    _ ≤ ∫ ξ : Space d, Real.exp (Real.pi^2*C^2)*G ξ :=
      setIntegral_le_integral (hG.const_mul _) (by filter_upwards with ξ; dsimp [G,f]; positivity)
    _ = Real.exp (Real.pi^2*C^2)*∫ ξ, G ξ := integral_const_mul _ _
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (fourier_gaussian_energy_bound μ hB hK hsk hb)
        (Real.exp_pos (Real.pi^2*C^2)).le
      simpa only [mul_assoc] using h

end Falconer

end OAI
