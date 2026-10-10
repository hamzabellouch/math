import OAI.Geometry.LatticeCovering.Desmoothing

namespace OAI

section

namespace SingleLatticeCovering.GaussianNumerics
open MeasureTheory Filter GaussianDensity GaussianProjection Asymptotics
open scoped Topology

noncomputable def A : ℝ := 1000+|Real.log (8*Real.pi)|+|Real.log Real.pi|
noncomputable def B : ℝ := 2*A+100
lemma A_pos : 0 < A := by unfold A; positivity
lemma A_large : 1000 ≤ A := by unfold A; linarith [abs_nonneg (Real.log (8*Real.pi)),abs_nonneg (Real.log Real.pi)]
lemma B_pos : 0 < B := by unfold B; linarith [A_pos]

lemma normalizer_log (D : ℕ) {b : ℝ} (hb : 0 < b) :
    normalizer D b=Real.exp ((D:ℝ)/2*Real.log (Real.pi/b)) := by
  rw [normalizer,Real.rpow_def_of_pos (by positivity),mul_comm]

lemma floor_inv_bound {l : ℕ} (hl : 1 ≤ l) :
    (densityFloor (l^4) (6*(l:ℝ)^2))⁻¹ ≤ Real.exp (A*(l:ℝ)^4) := by
  have ht : (1:ℝ) ≤ l := by exact_mod_cast hl
  have ht2 : 1 ≤ (l:ℝ)^2 := one_le_pow₀ ht
  have hlog : Real.log (8*Real.pi) ≤ 2*(A-392) := by
    have := le_abs_self (Real.log (8*Real.pi))
    unfold A
    linarith [abs_nonneg (Real.log (8*Real.pi)),abs_nonneg (Real.log Real.pi)]
  have hN := normalizer_pos (l^4) (by norm_num : (0:ℝ) < 1/8)
  rw [densityFloor,mul_inv_rev,inv_inv,←Real.exp_neg,normalizer_log _ (by norm_num),←Real.exp_add]
  push_cast
  apply Real.exp_le_exp.mpr
  have hR : (6*(l:ℝ)^2+1)^2 ≤ 49*(l:ℝ)^4 := by nlinarith [sq_nonneg ((l:ℝ)^2-1)]
  have hm := mul_le_mul_of_nonneg_left hlog (show 0 ≤ (l:ℝ)^4/2 by positivity)
  rw [show Real.pi/(1/8:ℝ)=8*Real.pi by ring]

  nlinarith

lemma floor_le_one (D : ℕ) (R : ℝ) : densityFloor D R ≤ 1 := by
  have hN : 1 ≤ normalizer D (1/8) := by
    unfold normalizer
    apply Real.one_le_rpow (by have := Real.pi_gt_three; linarith) (by positivity)
  unfold densityFloor
  exact (mul_le_of_le_one_left (Real.exp_pos _).le
    ((inv_le_one₀ (normalizer_pos D (by norm_num))).mpr hN)).trans
    (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (R+1)]))

lemma polynomial_exp_decay {p q : ℕ} (hpq : p < q) {a b : ℝ} (hb : 0 < b) :
    Tendsto (fun t : ℝ => Real.exp (a*t^p-b*t^q)) atTop (𝓝 0) := by
  have H := (isLittleO_pow_pow_atTop_of_lt (𝕜 := ℝ) hpq).const_mul_left a
  have ht : Tendsto (fun t : ℝ => Real.exp (-(b/2)*t^q)) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    have hh := (tendsto_pow_atTop (by omega : q ≠ 0) : Tendsto (fun t : ℝ => t^q) atTop atTop).const_mul_atTop (half_pos hb)
    simpa only [neg_mul,Function.comp_def] using tendsto_neg_atTop_atBot.comp hh
  apply squeeze_zero' (Filter.Eventually.of_forall (fun t => (Real.exp_pos _).le)) ?_ ht
  filter_upwards [H.bound (half_pos hb),eventually_ge_atTop (0:ℝ)] with t h ht
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg ht q)] at h
  apply Real.exp_le_exp.mpr
  linarith [le_abs_self (a*t^p)]

noncomputable def errBound (t : ℝ) := Real.exp (B*t^20-t^30)
noncomputable def tailBound (t : ℝ) := Real.exp ((A+10)*t^6-t^16/980000)
lemma errBound_tendsto : Tendsto errBound atTop (𝓝 0) := by
  change Tendsto (fun t : ℝ => Real.exp (B*t^20-t^30)) atTop (𝓝 0)
  simpa only [one_mul] using (polynomial_exp_decay (a := B) (p := 20) (q := 30) (by omega) (b := 1) (by norm_num))
lemma tailBound_tendsto : Tendsto tailBound atTop (𝓝 0) := by
  change Tendsto (fun t : ℝ => Real.exp ((A+10)*t^6-t^16/980000)) atTop (𝓝 0)
  convert (polynomial_exp_decay (a := A+10) (p := 6) (q := 16) (by omega) (b := 1/980000) (by norm_num)) using 1
  ext t
  congr 1
  ring

lemma gaussian_prefactor_bound {l D : ℕ} (hl : 1 ≤ l) (hD : D ≤ l^4) :
    (normalizer D (((l:ℝ)^10)^2/2))⁻¹*(l:ℝ)^10*Real.sqrt (D:ℝ) ≤ Real.exp (22*(l:ℝ)^5) := by
  have ht : (1:ℝ) ≤ l := by exact_mod_cast hl
  have ht0 : (0:ℝ) < l := lt_of_lt_of_le zero_lt_one ht
  have hr : 1 ≤ (l:ℝ)^10 := one_le_pow₀ ht
  have hp := normalizer_inv_bound D (pow_pos ht0 10)
  have hpd : ((l:ℝ)^10)^D ≤ ((l:ℝ)^10)^(l^4) := pow_le_pow_right₀ hr hD
  have hs : Real.sqrt (D:ℝ) ≤ (l:ℝ)^2 := (Real.sqrt_le_iff).mpr ⟨by positivity,by simpa only [←pow_mul,Nat.reduceMul] using (show (D:ℝ) ≤ (l:ℝ)^4 by exact_mod_cast hD)⟩
  calc
    _ ≤ (((l:ℝ)^10)^(l^4))*(l:ℝ)^10*(l:ℝ)^2 := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right (hp.trans hpd) (by positivity)) hs (Real.sqrt_nonneg _) (by positivity)
    _ = Real.exp (((l:ℝ)^4*10+12)*Real.log (l:ℝ)) := by
      rw [show (((l:ℝ)^4*10+12)*Real.log (l:ℝ))=
        (l^4:ℕ)*(10*Real.log (l:ℝ))+10*Real.log (l:ℝ)+2*Real.log (l:ℝ) by push_cast; ring,
        Real.exp_add,Real.exp_add,Real.exp_nat_mul]
      rw [show Real.exp (10*Real.log (l:ℝ))=(l:ℝ)^10 by simpa only [Nat.cast_ofNat,Real.exp_log ht0] using Real.exp_nat_mul (Real.log (l:ℝ)) 10,
        show Real.exp (2*Real.log (l:ℝ))=(l:ℝ)^2 by simpa only [Nat.cast_ofNat,Real.exp_log ht0] using Real.exp_nat_mul (Real.log (l:ℝ)) 2]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have ht4 : 1 ≤ (l:ℝ)^4 := one_le_pow₀ ht
      have hlog := Real.log_le_sub_one_of_pos ht0
      have hh := mul_le_mul_of_nonneg_left (show Real.log (l:ℝ) ≤ l by linarith) (show 0 ≤ (l:ℝ)^4*10+12 by positivity)
      nlinarith [mul_le_mul_of_nonneg_right ht4 ht0.le]

lemma volume_parameter_bound {l : ℕ} (hl : 1 ≤ l) :
    volume.real (Metric.closedBall (0:Isotropization.E (l^4)) ((l:ℝ)^10)) ≤
      Real.exp ((l:ℝ)^20+A*(l:ℝ)^4) := by
  have hlog : Real.log Real.pi ≤ 2*A := by
    unfold A
    linarith [le_abs_self (Real.log Real.pi),abs_nonneg (Real.log (8*Real.pi)),abs_nonneg (Real.log Real.pi)]
  apply (volume_closedBall_bound (l^4) (by positivity : 0 ≤ (l:ℝ)^10)).trans
  rw [normalizer_log _ (by norm_num),←Real.exp_add]
  push_cast
  apply Real.exp_le_exp.mpr
  simp only [div_one]
  have := mul_le_mul_of_nonneg_left hlog (show 0 ≤ (l:ℝ)^4/2 by positivity)
  nlinarith [show ((l:ℝ)^10)^2=(l:ℝ)^20 by ring]

end SingleLatticeCovering.GaussianNumerics

end

section
namespace SingleLatticeCovering.GaussianNumerics
open MeasureTheory Filter GaussianDensity GaussianProjection
open scoped Topology

lemma powerCoeff_bound {l : ℕ} (hl : 1 ≤ l) :
    22*(l:ℝ)^5+A*(l:ℝ)^4+(l:ℝ)^20 ≤ B*(l:ℝ)^20 := by
  have ht : (1:ℝ) ≤ l := by exact_mod_cast hl
  have h5 : (l:ℝ)^5 ≤ (l:ℝ)^20 := pow_le_pow_right₀ ht (by omega)
  have h4 : (l:ℝ)^4 ≤ (l:ℝ)^20 := pow_le_pow_right₀ ht (by omega)
  have hh := mul_le_mul_of_nonneg_left h4 A_pos.le
  dsimp [B]
  nlinarith [pow_nonneg (Nat.cast_nonneg l : (0:ℝ) ≤ l) 20,A_pos]

lemma uniform_error_bound {n l D : ℕ} (hn : 0 < n) (hl : 1 ≤ l) (hD : D ≤ l^4)
    (hroot : Real.exp ((l:ℝ)^30) ≤ Real.sqrt (Real.sqrt (n:ℝ))) :
    projectionError n D (1/Real.sqrt (n:ℝ)) ((l:ℝ)^10) ≤
      densityFloor D (6*(l:ℝ)^2)*errBound (l:ℝ) := by
  have ht : (0:ℝ) < l := by exact_mod_cast (show 0 < l by omega)
  have hq := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (show (0:ℝ) < n by exact_mod_cast hn))
  have hf := densityFloor_pos D (6*(l:ℝ)^2)
  rw [mul_comm (densityFloor D (6*(l:ℝ)^2))]
  apply (div_le_iff₀ hf).mp
  have hinv : (densityFloor D (6*(l:ℝ)^2))⁻¹ ≤ Real.exp (A*(l:ℝ)^4) :=
    (inv_anti₀ (densityFloor_pos (l^4) _) (densityFloor_dimension_mono hD _)).trans (floor_inv_bound hl)
  rw [root_error_identity hn (pow_nonneg ht.le 10),div_div,div_eq_mul_inv, mul_inv_rev]
  calc
    _ ≤ Real.exp (22*(l:ℝ)^5)* Real.exp (A*(l:ℝ)^4)*(Real.exp ((l:ℝ)^30))⁻¹ := by
      have hi := inv_anti₀ (Real.exp_pos ((l:ℝ)^30)) hroot
      have hp := gaussian_prefactor_bound hl hD
      rw [←mul_assoc]
      exact mul_le_mul (mul_le_mul hp hinv (inv_pos.mpr hf).le (Real.exp_pos _).le) hi (inv_pos.mpr hq).le (by positivity)
    _ = Real.exp (22*(l:ℝ)^5+A*(l:ℝ)^4-(l:ℝ)^30) := by rw [←Real.exp_neg,←Real.exp_add,←Real.exp_add]; rfl
    _ ≤ errBound (l:ℝ) := by
      apply Real.exp_le_exp.mpr
      have hh := powerCoeff_bound hl
      linarith [pow_nonneg ht.le 20]

lemma uniform_ball_error {n l : ℕ} (hn : 0 < n) (hl : 1 ≤ l)
    (hroot : Real.exp ((l:ℝ)^30) ≤ Real.sqrt (Real.sqrt (n:ℝ))) :
    projectionError n (l^4) (1/Real.sqrt (n:ℝ)) ((l:ℝ)^10)*
        volume.real (Metric.closedBall (0:Isotropization.E (l^4)) ((l:ℝ)^10)) ≤ errBound (l:ℝ) := by
  have ht : (0:ℝ) < l := by exact_mod_cast (show 0 < l by omega)
  have hq := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (show (0:ℝ) < n by exact_mod_cast hn))
  rw [root_error_identity hn (pow_nonneg ht.le 10),div_mul_eq_mul_div]
  calc
    _ ≤ (Real.exp (22*(l:ℝ)^5)*Real.exp ((l:ℝ)^20+A*(l:ℝ)^4))/Real.exp ((l:ℝ)^30) := by
      apply div_le_div₀ (by positivity) (by gcongr; exact gaussian_prefactor_bound hl le_rfl; exact volume_parameter_bound hl)
        (Real.exp_pos _) hroot
    _ = Real.exp (22*(l:ℝ)^5+A*(l:ℝ)^4+(l:ℝ)^20-(l:ℝ)^30) := by
      rw [div_eq_mul_inv,←Real.exp_neg,←Real.exp_add,←Real.exp_add]; congr 1; ring
    _ ≤ errBound (l:ℝ) := Real.exp_le_exp.mpr (sub_le_sub_right (powerCoeff_bound hl) _)

lemma kernel_normalizer_bound {l D : ℕ} (hl : 1 ≤ l) (hD : D ≤ l^4) :
    (normalizer D (((l:ℝ)^10)^2/2))⁻¹ ≤ Real.exp (10*(l:ℝ)^5) := by
  have ht : (1:ℝ) ≤ l := by exact_mod_cast hl
  have ht0 : (0:ℝ) < l := lt_of_lt_of_le zero_lt_one ht
  apply (normalizer_inv_bound D (pow_pos ht0 10)).trans
  apply (pow_le_pow_right₀ (one_le_pow₀ ht : 1 ≤ (l:ℝ)^10) hD).trans
  rw [←Real.exp_log (pow_pos (pow_pos ht0 10) (l^4)),Real.log_pow,Real.log_pow]
  apply Real.exp_le_exp.mpr
  push_cast
  have hh := mul_le_mul_of_nonneg_left (le_trans (Real.log_le_sub_one_of_pos ht0) (by linarith : (l:ℝ)-1 ≤ l))
    (show 0 ≤ 10*(l:ℝ)^4 by positivity)
  nlinarith

lemma tail_exponent_bound {l : ℕ} (hl : 1 ≤ l) :
    (l:ℝ)^16/980000 ≤ (((l:ℝ)^10)^2/2)*(localStep (6*(l:ℝ)^2))^2 := by
  have ht : (1:ℝ) ≤ l := by exact_mod_cast hl
  have ht2 : 1 ≤ (l:ℝ)^2 := one_le_pow₀ ht
  have hR : (6*(l:ℝ)^2+1)^2 ≤ 49*(l:ℝ)^4 := by nlinarith [sq_nonneg ((l:ℝ)^2-1)]
  unfold localStep
  have hd : 0 < 6*(l:ℝ)^2+1 := by positivity
  field_simp
  nlinarith [mul_le_mul_of_nonneg_left hR (show 0 ≤ (l:ℝ)^16 by positivity),
    show ((l:ℝ)^10)^2=(l:ℝ)^16*(l:ℝ)^4 by ring]

lemma uniform_tail_bound {l D : ℕ} (hl : 1 ≤ l) (hD : D ≤ l^4) :
    tailError D ((l:ℝ)^10) (6*(l:ℝ)^2) ≤ densityFloor D (6*(l:ℝ)^2)*tailBound (l:ℝ) := by
  have ht : (1:ℝ) ≤ l := by exact_mod_cast hl
  have hf := densityFloor_pos D (6*(l:ℝ)^2)
  rw [mul_comm (densityFloor D (6*(l:ℝ)^2))]
  apply (div_le_iff₀ hf).mp
  have hinv : (densityFloor D (6*(l:ℝ)^2))⁻¹ ≤ Real.exp (A*(l:ℝ)^4) :=
    (inv_anti₀ (densityFloor_pos (l^4) _) (densityFloor_dimension_mono hD _)).trans (floor_inv_bound hl)
  unfold tailError
  rw [div_eq_mul_inv]
  calc
    _ ≤ Real.exp (10*(l:ℝ)^5)*Real.exp (-(l:ℝ)^16/980000)*Real.exp (A*(l:ℝ)^4) := by
      apply mul_le_mul (mul_le_mul (kernel_normalizer_bound hl hD) (Real.exp_le_exp.mpr (by linarith [tail_exponent_bound hl]))
        (Real.exp_pos _).le (Real.exp_pos _).le) hinv (inv_pos.mpr hf).le (by positivity)
    _ = Real.exp (10*(l:ℝ)^5+A*(l:ℝ)^4-(l:ℝ)^16/980000) := by
      rw [←Real.exp_add,←Real.exp_add]; congr 1; ring
    _ ≤ tailBound (l:ℝ) := by
      apply Real.exp_le_exp.mpr
      have h5 : (l:ℝ)^5 ≤ (l:ℝ)^6 := pow_le_pow_right₀ ht (by omega)
      have h4 : (l:ℝ)^4 ≤ (l:ℝ)^6 := pow_le_pow_right₀ ht (by omega)
      nlinarith [mul_le_mul_of_nonneg_left h4 A_pos.le]

end SingleLatticeCovering.GaussianNumerics

end

section
namespace SingleLatticeCovering.GaussianNumerics
open MeasureTheory Filter GaussianDensity GaussianProjection
open scoped Topology

noncomputable def shellRate (t : ℝ) := 800*t*Real.exp (-t^2/180000)
noncomputable def denRate (t : ℝ) := Real.exp (-t^2/160000)
noncomputable def shellBound (t : ℝ) := 2*(shellRate t+2*(errBound t+2/t^16))

lemma shellRate_tendsto : Tendsto shellRate atTop (𝓝 0) := by
  have H := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1:ℝ) (1/180000) (by norm_num)
  have H' : Tendsto (fun t : ℝ => 800*(t*Real.exp (-(1/180000)*t))) atTop (𝓝 0) := by
    simpa only [Real.rpow_one,mul_zero] using H.const_mul 800
  change Tendsto (fun t : ℝ => 800*t*Real.exp (-t^2/180000)) atTop (𝓝 0)
  apply squeeze_zero' ?_ ?_ H'
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    exact mul_nonneg (mul_nonneg (by norm_num) ht) (Real.exp_pos _).le
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
    have ht0 : 0 ≤ t := by linarith
    rw [←mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    nlinarith

lemma denRate_tendsto : Tendsto denRate atTop (𝓝 0) := by
  have H : Tendsto (fun t : ℝ => t^2/160000) atTop atTop :=
    (tendsto_pow_atTop (by omega : (2:ℕ) ≠ 0)).atTop_div_const (by norm_num)
  change Tendsto (fun t : ℝ => Real.exp (-t^2/160000)) atTop (𝓝 0)
  simpa only [Function.comp_def,neg_div] using Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp H)

lemma shellBound_tendsto : Tendsto shellBound atTop (𝓝 0) := by
  have HP : Tendsto (fun t : ℝ => t^16) atTop atTop := tendsto_pow_atTop (by omega)
  have H : Tendsto (fun t : ℝ => 2/t^16) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_def] using
      ((tendsto_inv_atTop_zero.comp HP).const_mul (2:ℝ))
  change Tendsto (fun t : ℝ => 2*(shellRate t+2*(errBound t+2/t^16))) atTop (𝓝 0)
  simpa only [zero_add,add_zero,mul_zero] using
    (shellRate_tendsto.add ((errBound_tendsto.add H).const_mul 2)).const_mul 2

lemma shell_term_bound {l : ℕ} (hl : 2 ≤ l) :
    (4*((l^4-1:ℕ)+1:ℝ)/((l^4-1:ℕ)*(1/(100*(l:ℝ))))*
      Real.exp (-((l^4-1:ℕ):ℝ)*(1/(100*(l:ℝ)))^2/9)) ≤ shellRate (l:ℝ) := by
  have ht : (2:ℝ) ≤ l := by exact_mod_cast hl
  have ht0 : (0:ℝ) < l := by linarith
  have h4 : (2:ℝ) ≤ (l:ℝ)^4 := by nlinarith [sq_nonneg ((l:ℝ)^2-2),sq_nonneg ((l:ℝ)-2)]
  have hk : 1 ≤ l^4 := by exact_mod_cast (show (1:ℝ) ≤ (l:ℝ)^4 by linarith)
  have hm : ((l^4-1:ℕ):ℝ)=(l:ℝ)^4-1 := by rw [Nat.cast_sub hk,Nat.cast_pow,Nat.cast_one]
  rw [hm]
  have hp : 4*((l:ℝ)^4-1+1)/(((l:ℝ)^4-1)*(1/(100*(l:ℝ)))) ≤ 800*(l:ℝ) := by
    apply (div_le_iff₀ (mul_pos (by linarith : 0 < (l:ℝ)^4-1) (by positivity))).mpr
    have he : 800*(l:ℝ)*(((l:ℝ)^4-1)*(1/(100*(l:ℝ))))=8*((l:ℝ)^4-1) := by field_simp; ring
    rw [he]
    linarith
  have he : -((l:ℝ)^4-1)*(1/(100*(l:ℝ)))^2/9 ≤ -(l:ℝ)^2/180000 := by
    rw [show -((l:ℝ)^4-1)*(1/(100*(l:ℝ)))^2/9=-(((l:ℝ)^4-1)/(90000*(l:ℝ)^2)) by field_simp; ring,
      neg_div,neg_le_neg_iff]
    apply (le_div_iff₀ (by positivity : 0 < 90000*(l:ℝ)^2)).mpr
    nlinarith
  exact mul_le_mul hp (Real.exp_le_exp.mpr he) (Real.exp_pos _).le (by positivity)

lemma denominator_identity {l : ℕ} (hl : 1 ≤ l) :
    Real.exp (-((l^4:ℕ):ℝ)*(1/(100*(l:ℝ)))^2/16)=denRate (l:ℝ) := by
  have ht0 : (0:ℝ) < l := by exact_mod_cast (show 0 < l by omega)
  unfold denRate
  congr 1
  push_cast
  field_simp
  ring

lemma markov_term_bound {n l : ℕ} (hn : 0 < n) (hl : 1 ≤ l) :
    ((l^4:ℕ):ℝ)*((1/Real.sqrt (n:ℝ))^2*(n:ℝ)+1/((l:ℝ)^10)^2)/((l:ℝ)^10)^2 ≤ 2/(l:ℝ)^16 := by
  have ht : (1:ℝ) ≤ l := by exact_mod_cast hl
  have ht0 : (0:ℝ) < l := lt_of_lt_of_le zero_lt_one ht
  rw [normalization_second hn,Nat.cast_pow]
  have h1 : 1/((l:ℝ)^10)^2 ≤ 1 := (div_le_one (by positivity)).mpr (one_le_pow₀ (one_le_pow₀ ht))
  calc
    _ ≤ (l:ℝ)^4*2/((l:ℝ)^10)^2 := by gcongr; linarith
    _ = _ := by field_simp

lemma uniform_shell_bound {n l : ℕ} (hn : 0 < n) (hl : 2 ≤ l)
    (hroot : Real.exp ((l:ℝ)^30) ≤ Real.sqrt (Real.sqrt (n:ℝ)))
    (hden : denRate (l:ℝ) ≤ 1/2) :
    shellLoss n (l^4) (1/Real.sqrt (n:ℝ)) ((l:ℝ)^10) ((l:ℝ)^10) (1/(100*(l:ℝ))) ≤ shellBound (l:ℝ) := by
  have hl1 : 1 ≤ l := by omega
  have ht : (0:ℝ) < l := by exact_mod_cast (show 0 < l by omega)
  unfold shellLoss shellError
  rw [denominator_identity hl1]
  have hd : 0 < 1-denRate (l:ℝ) := by linarith
  apply (div_le_iff₀ hd).mpr
  have H := shell_term_bound hl
  have HE := uniform_ball_error hn hl1 hroot
  have HM := markov_term_bound hn hl1
  have hh : 0 ≤ shellRate (l:ℝ)+2*(errBound (l:ℝ)+2/(l:ℝ)^16) := by
    dsimp [shellRate,errBound]; positivity
  dsimp [shellBound]
  nlinarith

lemma uniform_numeric_conditions : ∀ᶠ l : ℕ in atTop,
    2 ≤ l ∧ denRate (l:ℝ) ≤ 1/2 ∧ errBound (l:ℝ) ≤ 1/128 ∧ tailBound (l:ℝ) ≤ 1/128 ∧
    shellBound (l:ℝ) < 1/(4*Prekopa.fourthMomentConstant) ∧ shellBound (l:ℝ) ≤ 1/8 := by
  have hfourth : 0 < Prekopa.fourthMomentConstant := Prekopa.fourthMomentConstant_pos
  have hnat : Tendsto (fun l : ℕ => (l:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (2:ℕ),
    (denRate_tendsto.comp hnat).eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1/2)),
    (errBound_tendsto.comp hnat).eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1/128)),
    (tailBound_tendsto.comp hnat).eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1/128)),
    (shellBound_tendsto.comp hnat).eventually (eventually_lt_nhds (by positivity : (0:ℝ) < 1/(4*Prekopa.fourthMomentConstant))),
    (shellBound_tendsto.comp hnat).eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1/8))]
    with l h1 h2 h3 h4 h5 h6
  exact ⟨h1,h2,h3,h4,h5,h6⟩

end SingleLatticeCovering.GaussianNumerics

end

section
namespace SingleLatticeCovering.GaussianNumerics
open MeasureTheory Filter Set GaussianDensity GaussianProjection CanonicalDensity
open scoped Topology ENNReal




theorem eventually_local_position : ∀ᶠ l : ℕ in atTop,
    ∀ m D : ℕ, D ≤ l → 0 < m+D →
      Real.exp ((l:ℝ)^30) ≤ Real.sqrt (Real.sqrt ((m+D : ℕ):ℝ)) →
      ∀ K : Set (E (m+D)), IsCompact K → Convex ℝ K → (interior K).Nonempty →
        ∃ e : E (m+D) ≃ᵃ[ℝ] ((Fin m → ℝ) × E D),
          ∀ y : E D, ‖y‖ ≤ 6*(l:ℝ)^2 → density (1/2) y/2 ≤ canonical (e '' K) y := by
  filter_upwards [uniform_numeric_conditions] with l hl
  obtain ⟨hl2,hden,herr,htail,hloss,hloss8⟩ := hl
  have hl1 : 1 ≤ l := by omega
  have ht : (1:ℝ) ≤ l := by exact_mod_cast hl1
  have ht0 : (0:ℝ) < l := lt_of_lt_of_le zero_lt_one ht
  have hl4 : l ≤ l^4 := Nat.le_self_pow (by omega) l
  have hk : 2 ≤ l^4 := hl2.trans hl4
  intro m D hD hn hroot K hK hc hi
  have hDk : D ≤ l^4 := hD.trans hl4
  obtain ⟨g,hJ,hJc,hJi,hprob,hmem,hiso,_,_,_⟩ := Isotropization.isotropic_logConcave_affine_body hK hc hi
  let := hprob
  have hε : (0:ℝ) < 1/(100*(l:ℝ)) := by positivity
  have hε1 : (1:ℝ)/(100*(l:ℝ)) ≤ 1/10 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hDε : (D:ℝ)*(1/(100*(l:ℝ))) ≤ 1/48 := by
    have hd : (D:ℝ) ≤ l := by exact_mod_cast hD
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hShell := uniform_shell_bound hn hl2 hroot hden
  have hErr := uniform_error_bound hn hl1 hDk hroot
  have hTail := uniform_tail_bound hl1 hDk
  have hf := densityFloor_pos D (6*(l:ℝ)^2)
  obtain ⟨u,hu,hu4,e,he⟩ := actual_canonical_lower hn hk hJ hJc hJi
    (Isotropization.uniformLaw (g '' K)) rfl hmem hiso (normalization_second hn)
    (one_le_pow₀ ht : 1 ≤ (l:ℝ)^10) (pow_pos ht0 10) hε hε1 hDε
    (show 0 ≤ 6*(l:ℝ)^2 by positivity) (hShell.trans_lt hloss) (hShell.trans hloss8)
    (hErr.trans (by nlinarith [mul_le_mul_of_nonneg_left herr hf.le]))
    (hTail.trans (by nlinarith [mul_le_mul_of_nonneg_left htail hf.le]))
  have hcomp : IsCompact (e '' (g '' K)) := hJ.image e.toContinuousLinearEquiv.continuous
  obtain ⟨S,hS⟩ := standardize_lower hcomp hu hu4 (show 0 ≤ 6*(l:ℝ)^2 by positivity) he
  refine ⟨g.trans (e.trans S).toAffineEquiv,fun y hy => ?_⟩
  have himage : (g.trans (e.trans S).toAffineEquiv) '' K=S '' (e '' (g '' K)) := by
    rw [Set.image_image,Set.image_image]
    rfl
  rw [himage]
  exact hS y hy


end SingleLatticeCovering.GaussianNumerics

end




end OAI
