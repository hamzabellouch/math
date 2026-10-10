import OAI.Analysis.IntegralMeans.CircleBounds

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology
namespace Brennan

def koebeMap (z : ℂ) : ℂ := z/(1-z)^2

lemma one_sub_ne_zero_disk {z : ℂ} (hz : z ∈ disk) : 1-z ≠ 0 := by
  have h : ‖z‖ < 1 := by simpa [disk] using hz
  intro he
  have : z = 1 := by linear_combination -he
  simp [this] at h

lemma koebeMap_hasDerivAt {z : ℂ} (hz : z ∈ disk) :
    HasDerivAt koebeMap ((1+z)/(1-z)^3) z := by
  have hn := one_sub_ne_zero_disk hz
  have h := (hasDerivAt_id z).div (((hasDerivAt_const z (1:ℂ)).sub (hasDerivAt_id z)).pow 2) (pow_ne_zero 2 hn)
  convert h using 1 <;> try rfl
  dsimp
  field_simp [hn]
  ring

lemma koebeMap_schlicht : Schlicht koebeMap := by
  refine ⟨⟨fun z hz => (koebeMap_hasDerivAt hz).differentiableAt.differentiableWithinAt,?_⟩,by simp [koebeMap],?_⟩
  · intro z hz w hw he
    have hnz := one_sub_ne_zero_disk hz
    have hnw := one_sub_ne_zero_disk hw
    have he' : (z-w)*(1-z*w) = 0 := by
      have hh := (div_eq_div_iff (pow_ne_zero 2 hnz) (pow_ne_zero 2 hnw)).mp he
      linear_combination hh
    have hzw : 1-z*w ≠ 0 := by
      have hz' : ‖z‖ < 1 := by simpa [disk] using hz
      have hw' : ‖w‖ < 1 := by simpa [disk] using hw
      have hn : ‖z*w‖ < 1 := by rw [norm_mul]; nlinarith [norm_nonneg z,norm_nonneg w]
      intro h
      have : z*w = 1 := by linear_combination -h
      simp [this] at hn
    exact sub_eq_zero.mp ((mul_eq_zero.mp he').resolve_right hzw)
  · simpa using (koebeMap_hasDerivAt (show (0:ℂ) ∈ disk by simp [disk])).deriv

lemma koebe_arc_deriv_bound {r θ : ℝ} (hr : 1/2 ≤ r) (hr1 : r < 1)
    (hθ : |θ| ≤ 1-r) : ‖deriv koebeMap (-circlePoint r θ)‖ ≤ 2*(1-r) := by
  have hr0 : 0 ≤ r := by linarith
  have hδ : 0 < 1-r := by linarith
  have hcos : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by
    have hp := Real.pi_gt_three; have := (abs_le.mp hθ).1; linarith,
    by have hp := Real.pi_gt_three; have := (abs_le.mp hθ).2; linarith⟩
  have he : ‖Complex.exp ((θ:ℂ)*Complex.I)-1‖ ≤ |θ| := by
    simpa [mul_comm] using (Real.norm_exp_I_mul_ofReal_sub_one_le (x := θ))
  have hnum : ‖1-circlePoint r θ‖ ≤ 2*(1-r) := by
    have hident : (1:ℂ)-circlePoint r θ = ((1-r:ℝ):ℂ)-(r:ℂ)*(Complex.exp ((θ:ℂ)*Complex.I)-1) := by
      simp only [circlePoint,Complex.ofReal_sub,Complex.ofReal_one]; ring
    rw [hident]
    calc
      _ ≤ ‖((1-r:ℝ):ℂ)‖+‖(r:ℂ)*(Complex.exp ((θ:ℂ)*Complex.I)-1)‖ := norm_sub_le _ _
      _ ≤ (1-r)+r*|θ| := by
        rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hδ,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr0]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left he hr0)
      _ ≤ 2*(1-r) := by nlinarith [abs_nonneg θ]
  have hden : 1 ≤ ‖1+circlePoint r θ‖ := by
    calc
      (1:ℝ) ≤ ((1:ℂ)+circlePoint r θ).re := by
        simp [circlePoint,Complex.exp_mul_I,Complex.mul_re]
        exact mul_nonneg hr0 hcos
      _ ≤ ‖1+circlePoint r θ‖ := Complex.re_le_norm _
  rw [(koebeMap_hasDerivAt (neg_circlePoint_mem_disk hr0 hr1 θ)).deriv,norm_div,norm_pow]
  simp only [← sub_eq_add_neg,sub_neg_eq_add]
  exact (div_le_self (norm_nonneg _) (one_le_pow₀ hden)).trans hnum

lemma koebe_arc_inverse_lower {r θ : ℝ} (hr : 1/2 ≤ r) (hr1 : r < 1)
    (hθ : |θ| ≤ 1-r) : 1/(4*(1-r)^2) ≤ ‖deriv koebeMap (-circlePoint r θ)‖^(-2:ℝ) := by
  have hn := norm_pos_iff.mpr (univalent_deriv_ne_zero Metric.isOpen_ball koebeMap_schlicht.1
    (neg_circlePoint_mem_disk (by linarith) hr1 θ))
  have hb := Real.rpow_le_rpow_of_nonpos hn (koebe_arc_deriv_bound hr hr1 hθ) (by norm_num : (-2:ℝ) ≤ 0)
  refine (show 1/(4*(1-r)^2) = (2*(1-r))^(-2:ℝ) by
    rw [Real.rpow_neg (by positivity),Real.rpow_two]; ring).trans_le hb

lemma koebe_mean_lower {r : ℝ} (hr : 1/2 ≤ r) (hr1 : r < 1) :
    1/(4*Real.pi*(1-r)) ≤ integralMean koebeMap (-2) r := by
  let F : ℝ → ℝ := fun θ => ‖deriv koebeMap (circlePoint r θ)‖^(-2:ℝ)
  let G : ℝ → ℝ := fun θ => ‖deriv koebeMap (-circlePoint r θ)‖^(-2:ℝ)
  have hF := (continuous_circle_deriv_rpow koebeMap_schlicht.1 (by linarith) hr1 (-2)).intervalIntegrable (μ := volume)
  have hG := (continuous_neg_circle_deriv_rpow koebeMap_schlicht.1 (by linarith) hr1 (-2)).intervalIntegrable (μ := volume)
  have hfull : (∫ θ in -Real.pi..Real.pi, G θ) = ∫ θ in -Real.pi..Real.pi, F θ := by
    have he (θ : ℝ) : G θ = F (θ+Real.pi) := by
      dsimp [G,F]
      congr 3
      simp [circlePoint,Complex.ofReal_add,add_mul,Complex.exp_add,Complex.exp_pi_mul_I]
    simp_rw [he]
    rw [intervalIntegral.integral_comp_add_right (f := F) Real.pi]
    have hp := ((periodic_circlePoint r).comp (fun z => ‖deriv koebeMap z‖^(-2:ℝ))).intervalIntegral_add_eq (-Real.pi) 0
    convert hp.symm using 1 <;> congr 1 <;> ring
  have hδ : 0 < 1-r := by linarith
  have hpart := intervalIntegral.integral_mono_on (by linarith : -(1-r) ≤ 1-r)
    (intervalIntegrable_const (a := -(1-r)) (b := 1-r) (c := 1/(4*(1-r)^2)))
    (hG (-(1-r)) (1-r)) (fun θ hθ => koebe_arc_inverse_lower hr hr1 (abs_le.mpr hθ))
  have heq : (∫ _ in -(1-r)..(1-r), 1/(4*(1-r)^2)) = 1/(2*(1-r)) := by
    rw [intervalIntegral.integral_const,smul_eq_mul]; field_simp; ring
  rw [heq] at hpart
  have hlarge := intervalIntegral.integral_mono_interval
    (by linarith [Real.pi_gt_three] : -Real.pi ≤ -(1-r)) (by linarith : -(1-r) ≤ 1-r)
    (by linarith [Real.pi_gt_three] : 1-r ≤ Real.pi)
    (Eventually.of_forall (fun θ => Real.rpow_nonneg (norm_nonneg (deriv koebeMap (-circlePoint r θ))) (-2))) (hG (-Real.pi) Real.pi)
  change _ ≤ integralMean koebeMap (-2) r
  calc
    _ = (2*Real.pi)⁻¹*(1/(2*(1-r))) := by field_simp; ring
    _ ≤ (2*Real.pi)⁻¹*(∫ θ in -Real.pi..Real.pi, G θ) :=
      mul_le_mul_of_nonneg_left (hpart.trans hlarge) (by positivity)
    _ = integralMean koebeMap (-2) r := by rw [hfull]; rfl

end Brennan

end

end OAI
