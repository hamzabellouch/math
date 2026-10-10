import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialGaugeEnergy

namespace OAI

/-! A vanishing weighted L2 factor times a bounded weighted L2 factor has
vanishing pairing. The proof uses Young's inequality on the fixed interval. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS

theorem spectralNorm_young (delta : ℝ) (hd : 0 < delta) (x y : ℂ) :
    ‖x‖*‖y‖ ≤ delta*‖x‖^2+‖y‖^2/(4*delta) := by
  apply (mul_le_mul_iff_right₀ (show 0 < 4*delta by positivity)).mp
  have hc : (‖y‖^2/(4*delta))*(4*delta)=‖y‖^2 := div_mul_cancel₀ _ (by positivity)
  nlinarith only [sq_nonneg (2*delta*‖x‖-‖y‖),hc]

theorem spectralYoung_pairing_limit (a : ℕ → ℂ) (b : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hb : Tendsto b atTop (𝓝 0))
    (hbound : ∀ delta : ℝ, 0 < delta → ∀ᶠ n in atTop, ‖a n‖ ≤ delta*B+b n/(4*delta)) :
    Tendsto a atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro epsilon he
  let delta := epsilon/(4*(B+1))
  have hd : 0 < delta := by dsimp only [delta]; positivity
  have hsmall : delta*B < epsilon/2 := by
    dsimp only [delta]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : 0 < 4*(B+1))).mpr
    nlinarith
  have ht : Tendsto (fun n => b n/(4*delta)) atTop (𝓝 0) := by
    simpa only [zero_div] using hb.div_const (4*delta)
  filter_upwards [hbound delta hd,ht.eventually (gt_mem_nhds (half_pos he))] with n hn hbn
  simpa only [dist_zero_right] using (hn.trans_lt (by linarith))

theorem spectralWeightedProduct_tendsto_zero (R C M : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (mu A : ℕ → ℝ → ℝ) (u v : ℕ → ℝ → ℂ)
    (hmu : ∀ n, ContinuousOn (mu n) (Icc 0 R)) (_hA : ∀ n, ContinuousOn (A n) (Icc 0 R))
    (hu : ∀ n, ContinuousOn (u n) (Icc 0 R)) (hv : ∀ n, ContinuousOn (v n) (Icc 0 R))
    (hmu0 : ∀ n r, r ∈ Icc 0 R → 0 ≤ mu n r)
    (hAbound : ∀ᶠ n in atTop, ∀ r ∈ Icc 0 R, |A n r| ≤ C*mu n r)
    (huBound : ∀ᶠ n in atTop, (∫ r in (0 : ℝ)..R, r^11*mu n r*‖u n r‖^2) ≤ M)
    (hvZero : Tendsto (fun n => ∫ r in (0 : ℝ)..R, r^11*mu n r*‖v n r‖^2) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ r in (0 : ℝ)..R, (r : ℂ)^11*(A n r : ℂ)*star (u n r)*v n r) atTop (𝓝 0) := by
  apply spectralYoung_pairing_limit _
    (fun n => C*(∫ r in (0 : ℝ)..R, r^11*mu n r*‖v n r‖^2)) (C*M) (mul_nonneg hC hM)
    (by simpa only [mul_zero] using hvZero.const_mul C)
  intro delta hd
  filter_upwards [hAbound,huBound] with n hAn hun
  let E := fun r => r^11*mu n r*‖u n r‖^2
  let V := fun r => r^11*mu n r*‖v n r‖^2
  have hEc : ContinuousOn E (Icc 0 R) := by dsimp only [E]; fun_prop
  have hVc : ContinuousOn V (Icc 0 R) := by dsimp only [V]; fun_prop
  have hpoint r (hr : r ∈ Ioc 0 R) :
      ‖(r : ℂ)^11*(A n r : ℂ)*star (u n r)*v n r‖ ≤ delta*C*E r+(C/(4*delta))*V r := by
    simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr.1.le,norm_star]
    have hm := hmu0 n r ⟨hr.1.le,hr.2⟩
    have h1 := mul_le_mul_of_nonneg_left (hAn r ⟨hr.1.le,hr.2⟩) (pow_nonneg hr.1.le 11)
    have h2 := spectralNorm_young delta hd (u n r) (v n r)
    have hh := mul_le_mul h1 h2 (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (mul_nonneg (pow_nonneg hr.1.le 11) (mul_nonneg hC hm))
    dsimp only [E,V]
    convert hh using 1 <;> ring
  have hi := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hR
    (Eventually.of_forall hpoint)
    (((hEc.const_mul (delta*C)).add (hVc.const_mul (C/(4*delta)))).intervalIntegrable_of_Icc hR)
  rw [intervalIntegral.integral_add,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hi
  · have hb := mul_le_mul_of_nonneg_left hun (mul_nonneg hd.le hC)
    dsimp only [E,V] at hi
    calc
      _ ≤ delta*C*M+(C/(4*delta))*(∫ r in (0 : ℝ)..R, r^11*mu n r*‖v n r‖^2) :=
        hi.trans (add_le_add hb le_rfl)
      _ = _ := by ring
  · exact (hEc.const_mul _).intervalIntegrable_of_Icc hR
  · exact (hVc.const_mul _).intervalIntegrable_of_Icc hR

end DefocusingNLS

end OAI
