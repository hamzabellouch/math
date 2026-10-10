import OAI.MeasureTheory.Falconer.Slicing.GaussianEnergy

namespace OAI

/-! # A broad Gaussian weight at the original finite spatial scale -/

namespace Falconer
open Set Metric MeasureTheory
variable {d : ℕ}

private theorem double_gaussian_mono (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ x, ∫ y, Real.exp (-b*‖x-y‖^2) ∂μ ∂μ) ≤
      ∫ x, ∫ y, Real.exp (-a*‖x-y‖^2) ∂μ ∂μ := by
  have hi (c : ℝ) (hc : 0 ≤ c) :
      Integrable (fun z : Space d × Space d => Real.exp (-c*‖z.1-z.2‖^2)) (μ.prod μ) := by
    apply (integrable_const (1:ℝ)).mono (by fun_prop)
    filter_upwards with z
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),norm_one]
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) (sq_nonneg _))
  rw [← integral_prod _ (hi b (ha.trans hab)),← integral_prod _ (hi a ha)]
  apply integral_mono (hi b (ha.trans hab)) (hi a ha)
  intro z
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_right hab (sq_nonneg ‖z.1-z.2‖)]

theorem gaussian_shell_energy_bound (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {B K s : ℝ} {k : ℕ} (hB : 0 < B) (hK : 0 ≤ K) (hsk : s ≤ k)
    (hb : ∀ x : Space d, ∀ r : ℝ, 1/B ≤ r →
      μ (ball x r) ≤ ENNReal.ofReal (K*r^s)) :
    (∫ ξ : Space d, Real.exp (-‖ξ‖^2/(16*B^2))*‖PlanarFalconer.sourceFourier μ ξ‖^2) ≤
      (16*Real.pi*B^2)^((d:ℝ)/2)*(μ.real univ*(K*(1/B)^s*gaussianBallConstant k)) := by
  have hb' : 0 < 1/(16*B^2) := by positivity
  have he (ξ : Space d) : -‖ξ‖^2/(16*B^2) = -(1/(16*B^2))*‖ξ‖^2 := by ring
  simp_rw [he]
  rw [PlanarFalconer.gaussian_lebesgue_square μ hb']
  have h₁ : Real.pi/(1/(16*B^2)) = 16*Real.pi*B^2 := by field_simp
  have h₂ : Real.pi^2/(1/(16*B^2)) = 16*Real.pi^2*B^2 := by field_simp
  rw [h₁,h₂]
  have hcoeff : B^2 ≤ 16*Real.pi^2*B^2 := by
    have hp : 1 ≤ Real.pi^2 := by nlinarith [Real.pi_gt_three]
    nlinarith [sq_nonneg B]
  have hm := double_gaussian_mono μ (sq_nonneg B) hcoeff
  have hd : (∫ x, ∫ y, Real.exp (-B^2*‖x-y‖^2) ∂μ ∂μ) =
      ∫ x, ∫ y, Real.exp (-(B*dist x y)^2) ∂μ ∂μ := by
    apply integral_congr_ae
    filter_upwards with x
    apply integral_congr_ae
    filter_upwards with y
    rw [dist_eq_norm]
    congr 1
    ring
  rw [hd] at hm
  have hfinal := hm.trans (gaussian_energy_bound μ hB hK hsk hb)
  have hdim : Module.finrank ℝ (Space d) = d := by simp [Space]
  simpa only [hdim] using mul_le_mul_of_nonneg_left hfinal
    (Real.rpow_nonneg (by positivity : 0 ≤ 16*Real.pi*B^2) ((d:ℝ)/2))


theorem gaussian_shell_energy_lintegral (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {B K s : ℝ} {k : ℕ} (hB : 0 < B) (hK : 0 ≤ K) (hsk : s ≤ k)
    (hb : ∀ x : Space d, ∀ r : ℝ, 1/B ≤ r →
      μ (ball x r) ≤ ENNReal.ofReal (K*r^s)) :
    (∫⁻ ξ : Space d, ENNReal.ofReal (Real.exp (-‖ξ‖^2/(16*B^2)))*
      ENNReal.ofReal (‖PlanarFalconer.sourceFourier μ ξ‖^2)) ≤
      ENNReal.ofReal ((16*Real.pi*B^2)^((d:ℝ)/2)*
        (μ.real univ*(K*(1/B)^s*gaussianBallConstant k))) := by
  have hi : Integrable (fun ξ : Space d => Real.exp (-‖ξ‖^2/(16*B^2))*
      ‖PlanarFalconer.sourceFourier μ ξ‖^2) := by
    have he (ξ : Space d) : -‖ξ‖^2/(16*B^2) = -(1/(16*B^2))*‖ξ‖^2 := by ring
    simp_rw [he]
    exact PlanarFalconer.gaussian_sourceFourier_integrable μ (by positivity : 0 < 1/(16*B^2))
  calc
    _ = ∫⁻ ξ : Space d, ENNReal.ofReal (Real.exp (-‖ξ‖^2/(16*B^2))*
        ‖PlanarFalconer.sourceFourier μ ξ‖^2) :=
      lintegral_congr (fun ξ => (ENNReal.ofReal_mul (Real.exp_pos _).le).symm)
    _ = ENNReal.ofReal (∫ ξ : Space d, Real.exp (-‖ξ‖^2/(16*B^2))*
        ‖PlanarFalconer.sourceFourier μ ξ‖^2) :=
      (ofReal_integral_eq_lintegral_ofReal hi (by filter_upwards with ξ; positivity)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (gaussian_shell_energy_bound μ hB hK hsk hb)

end Falconer

end OAI
