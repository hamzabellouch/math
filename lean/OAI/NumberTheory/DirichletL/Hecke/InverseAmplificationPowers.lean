import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationBudget

namespace OAI

noncomputable section
namespace SevenEighths.HeckeInverseAmplification

theorem amplified_norm_power (U A b p : ℝ) (hU : 0<U) :
    U*(b*(A*U^p))^6=(b*A)^6*U^(1+6*p) := by
  have h6 : (U^p)^6=U^(6*p) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hU.le]
    congr 1
    norm_num
    ring
  calc
    _ = (b*A)^6*(U^(1 : ℝ)*U^(6*p)) := by
      rw [show b*(A*U^p)=(b*A)*U^p by ring,mul_pow,h6,Real.rpow_one]
      ring
    _ = _ := by rw [←Real.rpow_add hU]

theorem amplified_energy_power (U A b p r κ : ℝ) (hU : 0<U) :
    (U*(b*(A*U^p))^6)*((U*(b*(A*U^p))^6)*U^r)^κ/(A*U^p)=
      ((b*A)^6*((b*A)^6)^κ/A)*U^(1+5*p+κ*(1+6*p+r)) := by
  rw [amplified_norm_power U A b p hU]
  have hHD : ((b*A)^6*U^(1+6*p))*U^r=(b*A)^6*U^(1+6*p+r) := by
    rw [mul_assoc,←Real.rpow_add hU]
  rw [hHD,Real.mul_rpow (by positivity) (Real.rpow_nonneg hU.le _),
    ←Real.rpow_mul hU.le]
  calc
    _ = ((b*A)^6*((b*A)^6)^κ/A)*
        ((U^(1+6*p)*U^((1+6*p+r)*κ))/U^p) := by ring
    _ = ((b*A)^6*((b*A)^6)^κ/A)*U^((1+6*p)+(1+6*p+r)*κ-p) := by
      rw [←Real.rpow_add hU,←Real.rpow_sub hU]
    _ = _ := by congr 2; ring

theorem fixed_multiplier_lower (U A p : ℝ) (hU : 1≤U) (hA : 0≤A) (hp : 0≤p) :
    A≤A*U^p := by
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.one_le_rpow hU hp) hA

theorem amplified_norm_dominates (U A b c r : ℝ) (hU : 1≤U) (hbA : 1≤b*A) :
    (U^r)^(1+c)≤U*(b*(A*U^(amplificationPower c r)))^6 := by
  have hUp : 0<U := zero_lt_one.trans_le hU
  rw [amplified_norm_power U A b _ hUp,←Real.rpow_mul hUp.le]
  have he : r*(1+c)≤1+6*amplificationPower c r := by
    have hh := le_max_right 0 (((1+c)*r-1)/6)
    unfold amplificationPower
    nlinarith
  have hp := Real.rpow_le_rpow_of_exponent_le hU he
  have hconst : (1 : ℝ)≤(b*A)^6 := one_le_pow₀ hbA
  exact hp.trans (le_mul_of_one_le_left (Real.rpow_nonneg hUp.le _) hconst)

end SevenEighths.HeckeInverseAmplification

end

end OAI
