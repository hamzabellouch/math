import Mathlib

namespace OAI

section

open Real Set MeasureTheory

namespace CAT0Fillings.RadialSobolev

lemma beta_integrand_coe (a b x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) :
    ((x^(a-1)*(1-x)^(b-1):ℝ):ℂ) =
      (x:ℂ)^((a:ℂ)-1)*(1-(x:ℂ))^((b:ℂ)-1) := by
  rw [Complex.ofReal_mul,Complex.ofReal_cpow hx.1,
    Complex.ofReal_cpow (sub_nonneg.mpr hx.2)]
  push_cast
  rfl

lemma beta_integrable {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun x : ℝ => x^(a-1)*(1-x)^(b-1)) volume 0 1 := by
  have hc := Complex.betaIntegral_convergent (u := (a:ℂ)) (v := (b:ℂ)) ha hb
  have hr : IntervalIntegrable
      (fun x : ℝ => ((x:ℂ)^((a:ℂ)-1)*(1-(x:ℂ))^((b:ℂ)-1)).re) volume 0 1 :=
    ⟨hc.1.re,hc.2.re⟩
  apply hr.congr_uIoo
  rw [uIoo_of_le zero_le_one]
  intro x hx
  dsimp only
  rw [←beta_integrand_coe a b x ⟨hx.1.le,hx.2.le⟩]
  rfl

lemma beta_integral {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ x in (0:ℝ)..1,x^(a-1)*(1-x)^(b-1)) = Real.Gamma a*Real.Gamma b/Real.Gamma (a+b) := by
  have he : Complex.betaIntegral (a:ℂ) (b:ℂ) =
      ((∫ x in (0:ℝ)..1,x^(a-1)*(1-x)^(b-1):ℝ):ℂ) := by
    rw [Complex.betaIntegral,←intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le zero_le_one]
    intro x hx
    exact (beta_integrand_coe a b x hx).symm
  have hc := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (a:ℂ)) (t := (b:ℂ)) ha hb
  rw [he,←Complex.ofReal_add,Complex.Gamma_ofReal,Complex.Gamma_ofReal,Complex.Gamma_ofReal,
    ←Complex.ofReal_mul,←Complex.ofReal_mul,Complex.ofReal_inj] at hc
  apply (eq_div_iff (ne_of_gt (Real.Gamma_pos_of_pos (add_pos ha hb)))).mpr
  linarith [hc]

end CAT0Fillings.RadialSobolev
end

section

open Real Set MeasureTheory

namespace CAT0Fillings.RadialSobolev

noncomputable def betaRadius (r : ℝ) := r^2/(1+r^2)

lemma betaRadius_deriv (r : ℝ) :
    HasDerivAt betaRadius (2*r/(1+r^2)^2) r := by
  have h : 1+r^2 ≠ 0 := ne_of_gt (by positivity)
  have hd := ((hasDerivAt_id r).pow 2).div
    ((hasDerivAt_const r 1).add ((hasDerivAt_id r).pow 2)) h
  dsimp only [id_eq, Pi.pow_apply, Pi.add_apply, Nat.cast_ofNat, Nat.reduceSub,
    pow_one, zero_add, mul_one] at hd
  convert hd using 1 <;> first | rfl | ring

lemma betaRadius_mono : MonotoneOn betaRadius (Ioi 0) := by
  intro x hx y hy hxy
  dsimp [betaRadius]
  apply (div_le_div_iff₀ (by positivity : 0 < 1+x^2) (by positivity : 0 < 1+y^2)).mpr
  have hsq : x^2 ≤ y^2 := sq_le_sq₀ (le_of_lt hx) (le_of_lt hy) |>.mpr hxy
  nlinarith

lemma betaRadius_image : betaRadius '' Ioi 0 = Ioo 0 1 := by
  ext t
  constructor
  · rintro ⟨r, hr, rfl⟩
    have hd : 0 < 1+r^2 := by positivity
    exact ⟨div_pos (sq_pos_of_pos hr) hd, (div_lt_one hd).mpr (by linarith)⟩
  · intro ht
    have hd : 0 < 1-t := sub_pos.mpr ht.2
    refine ⟨Real.sqrt (t/(1-t)), Real.sqrt_pos.2 (div_pos ht.1 hd), ?_⟩
    dsimp [betaRadius]
    rw [Real.sq_sqrt (div_nonneg ht.1.le hd.le)]
    field_simp
    ring

lemma bubble_substitution_algebra {a b r : ℝ} (hr : 0 < r) :
    (2*r/(1+r^2)^2)*((betaRadius r)^(a-1)*(1-betaRadius r)^(b-1)) =
      2*(r^(2*a-1)*(1+r^2)^(-(a+b))) := by
  have H : 0 < 1+r^2 := by positivity
  have he : 1-betaRadius r = 1/(1+r^2) := by dsimp [betaRadius]; field_simp; ring
  rw [he, betaRadius, Real.div_rpow (sq_nonneg _) H.le,
    Real.div_rpow zero_le_one H.le, Real.one_rpow]
  have he2 : (r^2)^(a-1) = r^(2*(a-1)) := by
    rw [←Real.rpow_natCast, ←Real.rpow_mul hr.le]
    norm_num
  rw [he2]
  rw [div_mul_div_comm]
  have hnum : r*r^(2*(a-1)) = r^(2*a-1) := by
    conv_lhs => lhs; rw [←Real.rpow_one r]
    rw [←Real.rpow_add hr]
    congr 1
    ring
  have hden : (1+r^2)^2*((1+r^2)^(a-1)*(1+r^2)^(b-1)) = (1+r^2)^(a+b) := by
    rw [←Real.rpow_natCast, ←Real.rpow_add H, ←Real.rpow_add H]
    congr 1
    ring
  calc
    _ = 2*(r*r^(2*(a-1)))/((1+r^2)^2*((1+r^2)^(a-1)*(1+r^2)^(b-1))) := by
      field_simp
    _ = 2*r^(2*a-1)/(1+r^2)^(a+b) := by rw [hnum,hden]
    _ = _ := by rw [Real.rpow_neg H.le]; ring

lemma bubble_integrable {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun r : ℝ => r^(2*a-1)*(1+r^2)^(-(a+b))) (Ioi 0) := by
  have hi : IntegrableOn (fun t : ℝ => t^(a-1)*(1-t)^(b-1)) (Ioo 0 1) :=
    (beta_integrable ha hb).1.mono_set Ioo_subset_Ioc_self
  rw [←betaRadius_image] at hi
  have h := (integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn
    measurableSet_Ioi (fun r _ => (betaRadius_deriv r).hasDerivWithinAt)
    betaRadius_mono _).mp hi
  have h' : IntegrableOn (fun r : ℝ => 2*(r^(2*a-1)*(1+r^2)^(-(a+b)))) (Ioi 0) := by
    apply h.congr_fun _ measurableSet_Ioi
    intro r hr
    exact bubble_substitution_algebra hr
  exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (by norm_num : (2:ℝ) ≠ 0)) _).mp h'

lemma bubble_integral {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ r in Ioi (0:ℝ), r^(2*a-1)*(1+r^2)^(-(a+b))) =
       Real.Gamma a*Real.Gamma b/(2*Real.Gamma (a+b)) := by
  have h := integral_image_eq_integral_deriv_smul_of_monotoneOn
    measurableSet_Ioi (fun r _ => (betaRadius_deriv r).hasDerivWithinAt)
    betaRadius_mono (fun t : ℝ => t^(a-1)*(1-t)^(b-1))
  rw [betaRadius_image] at h
  have he : (∫ r in Ioi (0:ℝ), (2*r/(1+r^2)^2) •
      ((betaRadius r)^(a-1)*(1-betaRadius r)^(b-1))) =
      2*∫ r in Ioi (0:ℝ), r^(2*a-1)*(1+r^2)^(-(a+b)) := by
    rw [←integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    exact bubble_substitution_algebra hr
  rw [he] at h
  have hb' := beta_integral ha hb
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo] at hb'
  rw [hb'] at h
  calc
    _ = (Real.Gamma a*Real.Gamma b/Real.Gamma (a+b))/2 := by linarith
    _ = _ := by ring

end CAT0Fillings.RadialSobolev
end

end OAI
