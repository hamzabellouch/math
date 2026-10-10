import OAI.NumberTheory.CubicMoment.Estimates.CubicBesselIntegral

namespace OAI

/-! Explicit exponential decay of the fixed cubic Bessel kernel, obtained
from its defining positive heat integral. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma cubicBessel_exponent_bound {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    -t-x/t ≤ -Real.sqrt x-(x/2)/t := by
  have he : 2*Real.sqrt x ≤ t+x/t := by
    have hs := sq_nonneg (t-Real.sqrt x)
    have hsq := Real.sq_sqrt hx.le
    calc
      _ ≤ (t^2+x)/t := (le_div_iff₀ ht).2 (by nlinarith)
      _ = t+x/t := by field_simp
  have hd : (x/2)/t = (x/t)/2 := by ring
  rw [hd]
  linarith

lemma cubicBesselHeat_exp_bound {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    cubicBesselHeat x t ≤ Real.exp (-Real.sqrt x)*
      (t^(-4/3:ℝ)*Real.exp (-(x/2)/t)) := by
  unfold cubicBesselHeat
  calc
    _ = t^(-4/3:ℝ)*Real.exp (-t-x/t) := by simp only [Real.exp_sub, neg_div, Real.exp_neg]; ring
    _ ≤ t^(-4/3:ℝ)*Real.exp (-Real.sqrt x-(x/2)/t) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (cubicBessel_exponent_bound hx ht))
        (Real.rpow_nonneg ht.le _)
    _ = _ := by simp only [Real.exp_sub, neg_div, Real.exp_neg]; ring

lemma cubicBesselKernel_exp_bound {x : ℝ} (hx : 0 < x) :
    cubicBesselKernel x ≤ x^(1/6:ℝ)*
      (Real.exp (-Real.sqrt x)*(Real.Gamma (1/3)*(x/2)^(-1/3:ℝ))) := by
  have hhalf : 0 < x/2 := by positivity
  have hi : IntegrableOn (fun t : ℝ => t^(-4/3:ℝ)*Real.exp (-(x/2)/t)) (Ioi 0) := by
    convert integrable_inverse_laplace_rpow (by norm_num : (0:ℝ) < 1/3) hhalf using 1; norm_num
  have hb := integral_mono_ae (cubicBesselHeat_integrable hx)
    (hi.const_mul (Real.exp (-Real.sqrt x))) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact cubicBesselHeat_exp_bound hx ht)
  unfold cubicBesselKernel
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hx.le _)
  apply hb.trans_eq
  rw [integral_const_mul]
  congr 1
  convert inverse_gaussian_moment (by norm_num : (0:ℝ) < 1/3) hhalf using 1 <;> norm_num

lemma cubicBessel_exp_prefactor {x : ℝ} (hx : 0 < x) :
    x^(1/6:ℝ)*(x/2)^(-1/3:ℝ) = 2^(1/3:ℝ)*x^(-1/6:ℝ) := by
  have he : ((2:ℝ)^(-1/3:ℝ))⁻¹ = 2^(1/3:ℝ) := by
    rw [←Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    ring
  have hd : x^(-1/3:ℝ) / 2^(-1/3:ℝ) = x^(-1/3:ℝ)*2^(1/3:ℝ) := by
    rw [div_eq_mul_inv,he]
  rw [Real.div_rpow hx.le (by norm_num : (0:ℝ) ≤ 2),hd]
  calc
    _ = 2^(1/3:ℝ)*(x^(1/6:ℝ)*x^(-1/3:ℝ)) := by ring
    _ = _ := by rw [←Real.rpow_add hx]; congr 1; norm_num

/-- A single exponential majorant for all positive arguments at least one. -/
theorem cubicBesselKernel_exponential_decay {x : ℝ} (hx : 1 ≤ x) :
    cubicBesselKernel x ≤ (Real.Gamma (1/3)*2^(1/3:ℝ))*Real.exp (-Real.sqrt x) := by
  have hxp : 0 < x := zero_lt_one.trans_le hx
  have hp : x^(-1/6:ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num)
  calc
    _ ≤ x^(1/6:ℝ)*(Real.exp (-Real.sqrt x)*(Real.Gamma (1/3)*(x/2)^(-1/3:ℝ))) :=
      cubicBesselKernel_exp_bound hxp
    _ = (Real.Gamma (1/3)*2^(1/3:ℝ))*Real.exp (-Real.sqrt x)*x^(-1/6:ℝ) := by
      calc
        _ = (Real.Gamma (1/3)*Real.exp (-Real.sqrt x))*(x^(1/6:ℝ)*(x/2)^(-1/3:ℝ)) := by ring
        _ = _ := by rw [cubicBessel_exp_prefactor hxp]; ring
    _ ≤ _ := mul_le_of_le_one_right (by positivity [Real.Gamma_pos_of_pos (by norm_num : (0:ℝ) < 1/3)]) hp

end CubicFirstMoment

end

end OAI
