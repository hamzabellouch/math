import Mathlib
import OAI.Geometry.CAT0Fillings.Bubble.Moments

namespace OAI

section

open Real Set MeasureTheory

namespace CAT0Fillings.RadialSobolev

lemma omega_gamma {k : ℕ} (hk : 0 < k) :
    omega k = Real.sqrt Real.pi ^ k / Real.Gamma ((k:ℝ)/2+1) := by
  let : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  rw [omega, EuclideanSpace.volume_ball]
  simp only [Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul]
  apply ENNReal.toReal_ofReal
  exact div_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (Real.Gamma_pos_of_pos (by positivity)).le

lemma polar_constant_gamma {n : ℕ} (hn : 0 < n) :
    (n:ℝ)*omega n = 2*Real.sqrt Real.pi^n/Real.Gamma ((n:ℝ)/2) := by
  have h : (0:ℝ) < n := by exact_mod_cast hn
  rw [omega_gamma hn,Real.Gamma_add_one (by positivity : (n:ℝ)/2 ≠ 0)]
  field_simp

lemma sphereArea_gamma (n : ℕ) :
    sphereArea n = 2*Real.sqrt Real.pi^(n+1)/Real.Gamma (((n:ℝ)+1)/2) := by
  have hh := polar_constant_gamma (Nat.succ_pos n)
  simpa [sphereArea,Nat.cast_add,Nat.cast_one] using hh

lemma bubble_mass_sphere {n : ℕ} (hn : 2 < n) :
    (2:ℝ)^n*((n:ℝ)*omega n*bubbleMass n) = sphereArea n := by
  have h : (2:ℝ) < n := by exact_mod_cast hn
  have G : Real.Gamma ((n:ℝ)/2) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have H : Real.Gamma ((n:ℝ)) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have J : Real.Gamma (((n:ℝ)+1)/2) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hd := Real.Gamma_mul_Gamma_add_half ((n:ℝ)/2)
  have e1 : (n:ℝ)/2+1/2 = ((n:ℝ)+1)/2 := by ring
  have e2 : 2*((n:ℝ)/2) = n := by ring
  rw [e1,e2, Real.rpow_sub (by norm_num : (0:ℝ) < 2), Real.rpow_one,Real.rpow_natCast] at hd
  rw [polar_constant_gamma (by omega),sphereArea_gamma,bubbleMass,pow_succ]
  apply (eq_div_iff J).mpr
  field_simp [G,H] at *
  have he := congrArg (fun x : ℝ => x*Real.sqrt Real.pi^n) hd
  rw [pow_succ]
  nlinarith [he]

end CAT0Fillings.RadialSobolev
end

section
open Set MeasureTheory

namespace CAT0Fillings.RadialSobolev

lemma integrable_euclidean_bubble {n : ℕ} (hn : 2 < n) :
    Integrable (fun x : Euc n => (1+‖x‖^2)^(-(n:ℝ))) volume := by
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  rw [integrable_fun_norm_addHaar (volume : Measure (Euc n)) (f := fun r : ℝ => (1+r^2)^(-(n:ℝ)))]
  simpa only [finrank_euclideanSpace,Fintype.card_fin,smul_eq_mul,←bubble_power_p hn] using
    (bubble_moments_integrable hn).1

lemma integral_euclidean_bubble {n : ℕ} (hn : 2 < n) :
    (∫ x : Euc n, (1+‖x‖^2)^(-(n:ℝ))) = sphereArea n/(2:ℝ)^n := by
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  rw [integral_fun_norm_addHaar (volume : Measure (Euc n)) (fun r : ℝ => (1+r^2)^(-(n:ℝ)))]
  simp only [finrank_euclideanSpace,Fintype.card_fin,smul_eq_mul,nsmul_eq_mul,←bubble_power_p hn]
  rw [(bubble_moments hn).1]
  have hc := bubble_mass_sphere hn
  change (n:ℝ)*(omega n*bubbleMass n) = _
  apply (eq_div_iff (by positivity)).mpr
  nlinarith [hc]
end CAT0Fillings.RadialSobolev
end

end OAI
