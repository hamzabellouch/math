import Mathlib

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.HodgeKernelBounds
open MeasureTheory Set

def rapidConstant (c : ℝ) (N : ℕ) : ℝ :=
  (N.factorial : ℝ) * Real.exp c / c^N

lemma rapidConstant_pos {c : ℝ} (hc : 0 < c) (N : ℕ) :
    0 < rapidConstant c N := by
  unfold rapidConstant
  positivity

lemma exp_neg_le_rapid {c a : ℝ} (hc : 0 < c) (ha : 0 ≤ a) (N : ℕ) :
    Real.exp (-c*a) ≤ rapidConstant c N / (1+a)^N := by
  have hpa : 0 < (1+a)^N := pow_pos (by linarith) _
  have hpc : 0 < c^N := pow_pos hc _
  have hf : 0 < (N.factorial : ℝ) := by positivity
  have hp := (div_le_iff₀ hf).mp
    (Real.pow_div_factorial_le_exp (c*(1+a)) (by positivity) N)
  apply (le_div_iff₀ hpa).mpr
  apply (le_div_iff₀ hpc).mpr
  calc
    Real.exp (-c*a) * (1+a)^N * c^N = (c*(1+a))^N * Real.exp (-c*a) := by
      rw [mul_pow]; ring
    _ ≤ ((N.factorial : ℝ) * Real.exp (c*(1+a))) * Real.exp (-c*a) :=
      mul_le_mul_of_nonneg_right (by simpa only [mul_comm] using hp) (Real.exp_pos _).le
    _ = (N.factorial : ℝ) * Real.exp c := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

def moment (n : ℕ) (b : ℝ) : ℝ := (1/b)^(n+1) * (n.factorial : ℝ)

lemma moment_integrable (n : ℕ) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun s : ℝ => s^n * Real.exp (-(b*s))) (Ioi 0) := by
  simpa only [Real.rpow_one, Real.rpow_natCast, neg_mul] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n:ℝ)) (p := 1)
      (by have := Nat.cast_nonneg (α := ℝ) n; linarith) (by norm_num) hb)

lemma moment_integral (n : ℕ) {b : ℝ} (hb : 0 < b) :
    (∫ s : ℝ in Ioi 0, s^n * Real.exp (-(b*s))) = moment n b := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (n:ℝ)+1)
    (by positivity) hb
  simp_rw [add_sub_cancel_right, Real.rpow_natCast, Real.Gamma_nat_eq_factorial] at h
  have he : (n:ℝ)+1 = ((n+1:ℕ):ℝ) := by push_cast; rfl
  rw [he, Real.rpow_natCast] at h
  exact h

lemma moment_pos (n : ℕ) {b : ℝ} (hb : 0 < b) : 0 < moment n b := by
  unfold moment
  positivity

def profile (n : ℕ) (c a s : ℝ) : ℝ :=
  Real.exp (-s) * s^n * Real.exp (-c*a^2/s)

lemma profile_nonneg (n : ℕ) (c a : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ profile n c a s := by
  unfold profile
  positivity

lemma gaussian_exponent_split {c a s : ℝ} (hc : 0 < c) (hs : 0 < s) :
    -s - c*a^2/s ≤ -(s/2) - 2*(min (1/2) c)*a := by
  let k := min (1/2 : ℝ) c
  have hk : 0 ≤ k := le_of_lt (lt_min (by norm_num) hc)
  have hk₁ : k ≤ 1/2 := min_le_left _ _
  have hk₂ : k ≤ c := min_le_right _ _
  have hsq := mul_nonneg hk (sq_nonneg (s-a))
  have ht := mul_nonneg (sub_nonneg.mpr hk₁) (sq_nonneg s)
  have hu := mul_nonneg (sub_nonneg.mpr hk₂) (sq_nonneg a)
  have h : 2*k*a*s ≤ s^2/2+c*a^2 := by nlinarith
  have hd := (div_le_div_of_nonneg_right h hs.le)
  have he : (2*k*a*s)/s = 2*k*a := by field_simp
  have he' : (s^2/2+c*a^2)/s = s/2+c*a^2/s := by field_simp
  rw [he,he'] at hd
  change -s-c*a^2/s ≤ -(s/2)-2*k*a
  linarith

lemma profile_le_exp (n : ℕ) {c a s : ℝ} (hc : 0 < c) (hs : 0 < s) :
    profile n c a s ≤
      (s^n * Real.exp (-((1/2)*s))) * Real.exp (-(2*min (1/2) c)*a) := by
  unfold profile
  have h := Real.exp_le_exp.mpr (gaussian_exponent_split (a := a) hc hs)
  have he : Real.exp (-s) * Real.exp (-c*a^2/s) = Real.exp (-s-c*a^2/s) := by
    rw [← Real.exp_add]; congr 1; ring
  have he' : Real.exp (-(s/2)-2*min (1/2) c*a) =
      Real.exp (-((1/2)*s)) * Real.exp (-(2*min (1/2) c)*a) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [← he,he'] at h
  have hp := mul_le_mul_of_nonneg_left h (pow_nonneg hs.le n)
  nlinarith only [hp]

lemma profile_integrable (n : ℕ) {c a : ℝ} (hc : 0 < c) :
    IntegrableOn (profile n c a) (Ioi 0) := by
  apply ((moment_integrable n (by norm_num : (0:ℝ)<1/2)).mul_const
    (Real.exp (-(2*min (1/2) c)*a))).mono' (by
      unfold profile
      exact (by fun_prop : Measurable _).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  rw [Real.norm_eq_abs, abs_of_nonneg (profile_nonneg _ _ _ hs.le)]
  exact profile_le_exp n hc hs

lemma profile_integral_le_exp (n : ℕ) {c a : ℝ} (hc : 0 < c) :
    (∫ s : ℝ in Ioi 0, profile n c a s) ≤
      moment n (1/2) * Real.exp (-(2*min (1/2) c)*a) := by
  calc
    _ ≤ ∫ s : ℝ in Ioi 0,
        (s^n * Real.exp (-((1/2)*s))) * Real.exp (-(2*min (1/2) c)*a) := by
      apply integral_mono_ae (profile_integrable n hc)
        ((moment_integrable n (by norm_num : (0:ℝ)<1/2)).mul_const _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact profile_le_exp n hc hs
    _ = _ := by rw [integral_mul_const, moment_integral n (by norm_num : (0:ℝ)<1/2)]

lemma profile_integral_le_rapid (n N : ℕ) {c a : ℝ} (hc : 0 < c) (ha : 0 ≤ a) :
    (∫ s : ℝ in Ioi 0, profile n c a s) ≤
      (moment n (1/2) * rapidConstant (2*min (1/2) c) N) / (1+a)^N := by
  have hk : 0 < 2*min (1/2) c := mul_pos (by norm_num) (lt_min (by norm_num) hc)
  calc
    _ ≤ moment n (1/2) * Real.exp (-(2*min (1/2) c)*a) := profile_integral_le_exp n hc
    _ ≤ moment n (1/2) * (rapidConstant (2*min (1/2) c) N / (1+a)^N) :=
      mul_le_mul_of_nonneg_left (exp_neg_le_rapid hk ha N)
        (moment_pos n (by norm_num : (0:ℝ)<1/2)).le
    _ = _ := by ring

def truncatedProfile (n : ℕ) (c a T : ℝ) : ℝ :=
  ∫ s : ℝ in Ioc 0 T, profile n c a s

lemma truncatedProfile_nonneg (n : ℕ) (c a T : ℝ) :
    0 ≤ truncatedProfile n c a T := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  exact profile_nonneg n c a hs.1.le

lemma truncatedProfile_le (n : ℕ) {c a : ℝ} (hc : 0 < c) (T : ℝ) :
    truncatedProfile n c a T ≤ ∫ s : ℝ in Ioi 0, profile n c a s := by
  apply setIntegral_mono_set (profile_integrable n hc)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact profile_nonneg n c a hs.le
  · exact Filter.Eventually.of_forall (fun _ hs => hs.1)

lemma leading_profile_lower {a s : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1)
    (hs : s ∈ Icc (1:ℝ) 2) :
    Real.exp (-(9/4 : ℝ)) ≤ profile 3 (1/4) a s := by
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs.1
  have hsa : a^2 ≤ s := (pow_le_one₀ ha ha').trans hs.1
  have hexp : -(1/4 : ℝ) ≤ -(1/4)*a^2/s := by
    apply (le_div_iff₀ hs0).mpr
    nlinarith
  have hs3 : (1:ℝ) ≤ s^3 := one_le_pow₀ hs.1
  have hsExp : Real.exp (-(2:ℝ)) ≤ Real.exp (-s) := Real.exp_le_exp.mpr (by linarith [hs.2])
  have haExp := Real.exp_le_exp.mpr hexp
  calc
    Real.exp (-(9/4 : ℝ)) = (Real.exp (-(2:ℝ)) * 1) * Real.exp (-(1/4:ℝ)) := by
      rw [mul_one, ← Real.exp_add]; congr 1; norm_num
    _ ≤ (Real.exp (-s) * s^3) * Real.exp (-(1/4)*a^2/s) :=
      mul_le_mul (mul_le_mul hsExp hs3 (by norm_num) (Real.exp_pos _).le)
        haExp (Real.exp_pos _).le (by positivity)
    _ = profile 3 (1/4) a s := rfl

lemma truncatedProfile_lower {a T : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1)
    (hT : 2 ≤ T) :
    Real.exp (-(9/4 : ℝ)) ≤ truncatedProfile 3 (1/4) a T := by
  have hsub : Icc (1:ℝ) 2 ⊆ Ioc (0:ℝ) T := by
    intro s hs
    exact ⟨lt_of_lt_of_le zero_lt_one hs.1, hs.2.trans hT⟩
  have hI := (profile_integrable 3 (a := a) (by norm_num : (0:ℝ)<1/4)).mono_set
    (show Ioc (0:ℝ) T ⊆ Ioi 0 from fun _ h => h.1)
  calc
    _ = ∫ _ : ℝ in Icc (1:ℝ) 2, Real.exp (-(9/4 : ℝ)) := by
      norm_num [setIntegral_const]
    _ ≤ ∫ s : ℝ in Icc (1:ℝ) 2, profile 3 (1/4) a s := by
      apply integral_mono_ae
        ((continuous_const : Continuous (fun _ : ℝ => Real.exp (-(9/4 : ℝ)))).continuousOn.integrableOn_Icc)
        (hI.mono_set hsub)
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      exact leading_profile_lower ha ha' hs
    _ ≤ truncatedProfile 3 (1/4) a T := by
      apply setIntegral_mono_set hI
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        exact profile_nonneg _ _ _ hs.1.le
      · exact Filter.Eventually.of_forall hsub

def leading (r t₀ d : ℝ) : ℝ :=
  (1 / (120*(4*Real.pi)^2)) * (r⁻¹)^4 *
    truncatedProfile 3 (1/4) (d/r) (t₀/r^2)

def leadingConstant (N : ℕ) : ℝ :=
  (1 / (120*(4*Real.pi)^2)) * moment 3 (1/2) * rapidConstant (1/2) N

lemma leadingConstant_pos (N : ℕ) : 0 < leadingConstant N := by
  unfold leadingConstant
  have := moment_pos 3 (by norm_num : (0:ℝ)<1/2)
  have := rapidConstant_pos (by norm_num : (0:ℝ)<1/2) N
  positivity

lemma leading_nonneg (r t₀ d : ℝ) : 0 ≤ leading r t₀ d := by
  unfold leading
  exact mul_nonneg (by positivity) (truncatedProfile_nonneg _ _ _ _)

lemma leading_upper (N : ℕ) {r d : ℝ} (hr : 0 < r) (hd : 0 ≤ d) (t₀ : ℝ) :
    leading r t₀ d ≤ leadingConstant N * (r⁻¹)^4 / (1+d/r)^N := by
  have h := (truncatedProfile_le 3 (a := d/r) (by norm_num : (0:ℝ)<1/4) (t₀/r^2)).trans
    (profile_integral_le_rapid 3 N (by norm_num : (0:ℝ)<1/4) (div_nonneg hd hr.le))
  norm_num only [show min (1/2 : ℝ) (1/4) = 1/4 by norm_num,
    show (2:ℝ)*(1/4) = 1/2 by norm_num] at h
  have hp := mul_le_mul_of_nonneg_left h
    (show 0 ≤ (1 / (120*(4*Real.pi)^2)) * (r⁻¹)^4 by positivity)
  unfold leading leadingConstant
  convert hp using 1
  first | rfl | ring

lemma leading_lower {r d t₀ : ℝ} (hr : 0 < r) (hd : 0 ≤ d) (hdr : d ≤ r)
    (ht₀ : 2*r^2 ≤ t₀) :
    ((1 / (120*(4*Real.pi)^2)) * Real.exp (-(9/4 : ℝ))) * (r⁻¹)^4 ≤ leading r t₀ d := by
  have h := truncatedProfile_lower (div_nonneg hd hr.le) ((div_le_one hr).mpr hdr)
    ((le_div_iff₀ (sq_pos_of_pos hr)).mpr ht₀)
  have hp := mul_le_mul_of_nonneg_left h
    (show 0 ≤ (1 / (120*(4*Real.pi)^2)) * (r⁻¹)^4 by positivity)
  unfold leading
  convert hp using 1
  first | rfl | ring

def gaussianError (c r d : ℝ) : ℝ :=
  (1/120 : ℝ) * (r⁻¹)^2 * ∫ s : ℝ in Ioi 0, profile 4 c (d/r) s

lemma gaussianError_upper (N : ℕ) {c r d : ℝ} (hc : 0 < c) (hr : 0 < r) (hd : 0 ≤ d) :
    gaussianError c r d ≤
      ((1/120 : ℝ) * moment 4 (1/2) * rapidConstant (2*min (1/2) c) N) *
        (r⁻¹)^2 / (1+d/r)^N := by
  have h := profile_integral_le_rapid 4 N hc (div_nonneg hd hr.le)
  have hp := mul_le_mul_of_nonneg_left h
    (show 0 ≤ (1/120 : ℝ) * (r⁻¹)^2 by positivity)
  unfold gaussianError
  convert hp using 1
  first | rfl | ring

def gammaTail (T : ℝ) : ℝ := ∫ s : ℝ in Ioi T, Real.exp (-s) * s^5

lemma gammaTail_nonneg {T : ℝ} (hT : 0 ≤ T) : 0 ≤ gammaTail T := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact mul_nonneg (Real.exp_pos _).le (pow_nonneg (hT.trans hs.le) _)

lemma gammaTail_le {T : ℝ} (hT : 0 ≤ T) :
    gammaTail T ≤ moment 5 (1/2) * Real.exp (-(T/2)) := by
  have hi := (moment_integrable 5 (by norm_num : (0:ℝ)<1)).mono_set
    (show Ioi T ⊆ Ioi (0:ℝ) from fun _ hs => hT.trans_lt hs)
  have hj := (moment_integrable 5 (by norm_num : (0:ℝ)<1/2)).mono_set
    (show Ioi T ⊆ Ioi (0:ℝ) from fun _ hs => hT.trans_lt hs)
  calc
    gammaTail T ≤ ∫ s : ℝ in Ioi T, (s^5 * Real.exp (-((1/2)*s))) * Real.exp (-(T/2)) := by
      apply integral_mono_ae (by simpa only [IntegrableOn, mul_comm, one_mul, mul_one] using hi)
        (hj.mul_const _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have he : Real.exp (-s) ≤ Real.exp (-((1/2)*s)) * Real.exp (-(T/2)) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith [show T < s from hs])
      simpa only [mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_of_nonneg_right he (pow_nonneg (hT.trans hs.le) 5)
    _ ≤ ∫ s : ℝ in Ioi 0, (s^5 * Real.exp (-((1/2)*s))) * Real.exp (-(T/2)) := by
      apply setIntegral_mono_set ((moment_integrable 5 (by norm_num : (0:ℝ)<1/2)).mul_const _)
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        have hs0 : 0 < s := hs
        positivity
      · exact Filter.Eventually.of_forall (fun _ hs => hT.trans_lt hs)
    _ = moment 5 (1/2) * Real.exp (-(T/2)) := by
      rw [integral_mul_const, moment_integral 5 (by norm_num : (0:ℝ)<1/2)]

lemma exp_neg_le_power {a : ℝ} (ha : 0 < a) (n : ℕ) :
    Real.exp (-a) ≤ (n.factorial : ℝ) / a^n := by
  apply (le_div_iff₀ (pow_pos ha n)).mpr
  have h := (div_le_iff₀ (show 0 < (n.factorial : ℝ) by positivity)).mp
    (Real.pow_div_factorial_le_exp a ha.le n)
  calc
    Real.exp (-a) * a^n ≤ Real.exp (-a) * ((n.factorial : ℝ)*Real.exp a) :=
      mul_le_mul_of_nonneg_left (by simpa only [mul_comm] using h) (Real.exp_pos _).le
    _ = (n.factorial : ℝ) := by rw [mul_left_comm, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]

lemma gammaTail_small_scale (M : ℕ) {t₀ r : ℝ} (ht₀ : 0 < t₀) (hr : 0 < r) :
    gammaTail (t₀/r^2) ≤
      (moment 5 (1/2) * (M.factorial : ℝ) * (2/t₀)^M) * r^(2*M) := by
  have h := (gammaTail_le (div_nonneg ht₀.le (sq_nonneg r))).trans
    (mul_le_mul_of_nonneg_left
      (exp_neg_le_power (show 0 < t₀/r^2/2 by positivity) M)
      (moment_pos 5 (by norm_num : (0:ℝ)<1/2)).le)
  calc
    _ ≤ moment 5 (1/2) * ((M.factorial : ℝ) / (t₀/r^2/2)^M) := h
    _ = _ := by
      rw [div_pow, div_pow, pow_mul, div_pow]
      field_simp

lemma power_absorb {r d D : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1)
    (hd : 0 ≤ d) (hdD : d ≤ D) (M N : ℕ) (hMN : N ≤ 2*M+2) :
    r^(2*M) ≤ (1+D)^N * (r⁻¹)^2 / (1+d/r)^N := by
  have hD : 0 ≤ D := hd.trans hdD
  have hrd : 0 < r+d := add_pos_of_pos_of_nonneg hr hd
  have h1 : 0 < 1+d/r := by positivity
  have hpow : r^(2*M+2) ≤ r^N := pow_le_pow_of_le_one hr.le hr₁ hMN
  have hrdD : (r+d)^N ≤ (1+D)^N := pow_le_pow_left₀ hrd.le (add_le_add hr₁ hdD) N
  have he : (1+d/r)^N = (r+d)^N / r^N := by
    rw [← div_pow]; congr 1; field_simp
  rw [he, div_div_eq_mul_div]
  apply (le_div_iff₀ (pow_pos hrd N)).mpr
  calc
    r^(2*M) * (r+d)^N ≤ r^(2*M) * (1+D)^N :=
      mul_le_mul_of_nonneg_left hrdD (pow_nonneg hr.le _)
    _ ≤ ((1+D)^N * (r⁻¹)^2) * r^N := by
      have h := mul_le_mul_of_nonneg_right hpow
        (show 0 ≤ (1+D)^N * (r⁻¹)^2 by positivity)
      calc
        r^(2*M) * (1+D)^N = r^(2*M+2) * ((1+D)^N * (r⁻¹)^2) := by
          rw [pow_add]
          field_simp
        _ ≤ r^N * ((1+D)^N * (r⁻¹)^2) := h
        _ = _ := by ring

lemma gaussianError_nonneg {c r d : ℝ} : 0 ≤ gaussianError c r d := by
  unfold gaussianError
  apply mul_nonneg (by positivity)
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact profile_nonneg 4 c (d/r) hs.le

lemma gammaTail_spatial (M N : ℕ) {t₀ r d D : ℝ} (ht₀ : 0 < t₀)
    (hr : 0 < r) (hr₁ : r ≤ 1) (hd : 0 ≤ d) (hdD : d ≤ D) (hMN : N ≤ 2*M+2) :
    gammaTail (t₀/r^2) ≤
      (moment 5 (1/2) * (M.factorial : ℝ) * (2/t₀)^M * (1+D)^N) *
        (r⁻¹)^2 / (1+d/r)^N := by
  calc
    _ ≤ (moment 5 (1/2) * (M.factorial : ℝ) * (2/t₀)^M) * r^(2*M) :=
      gammaTail_small_scale M ht₀ hr
    _ ≤ (moment 5 (1/2) * (M.factorial : ℝ) * (2/t₀)^M) *
        ((1+D)^N * (r⁻¹)^2 / (1+d/r)^N) :=
      mul_le_mul_of_nonneg_left (power_absorb hr hr₁ hd hdD M N hMN) (by
        have := moment_pos 5 (by norm_num : (0:ℝ)<1/2)
        positivity)
    _ = _ := by ring

end TamingCompatibility.GeometricHilbert.HodgeKernelBounds

end
end

end

end OAI
