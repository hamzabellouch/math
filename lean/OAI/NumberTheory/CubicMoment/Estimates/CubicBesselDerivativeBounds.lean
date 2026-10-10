import OAI.NumberTheory.CubicMoment.Estimates.CubicBesselDerivative
import OAI.NumberTheory.CubicMoment.Estimates.CubicBesselPowerDecay

namespace OAI

/-! Power decay of the first derivative of the fixed Bessel kernel.
The same lattice majorants can therefore control vertical theta derivatives. -/
noncomputable section
open MeasureTheory Set Filter
namespace CubicFirstMoment

lemma cubicBesselHeatDerivative_integrable {x : ℝ} (hx : 0<x) :
    IntegrableOn (cubicBesselHeatDerivative x) (Ioi 0) := by
  have hi : IntegrableOn (fun t : ℝ => t^(-7/3:ℝ)*Real.exp (-x/t)) (Ioi 0) := by
    convert integrable_inverse_laplace_rpow (by norm_num : (0:ℝ)<4/3) hx using 1
    norm_num
  apply hi.mono' (by
    apply Measurable.aestronglyMeasurable
    unfold cubicBesselHeatDerivative cubicBesselHeat
    fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact cubicBesselHeatDerivative_local_bound le_rfl ht

lemma cubicBesselHeatDerivative_power_bound (k : ℕ) {x t : ℝ}
    (hx : 0<x) (ht : 0<t) :
    ‖cubicBesselHeatDerivative x t‖≤((k+1).factorial:ℝ)/x^(k+1)*
      (t^((k:ℝ)-4/3)*Real.exp (-t)) := by
  have h := div_le_div_of_nonneg_right (cubicBesselHeat_power_bound (k+1) hx ht) ht.le
  have hp : t^((k+1:ℕ)-4/3:ℝ)/t=t^((k:ℝ)-4/3) := by
    calc
      _ = t^((k+1:ℕ)-4/3:ℝ)/t^(1:ℝ) := by rw [Real.rpow_one]
      _ = t^(((k+1:ℕ)-4/3:ℝ)-1) := (Real.rpow_sub ht _ _).symm
      _ = _ := by congr 1; push_cast; ring
  simp only [cubicBesselHeatDerivative,norm_div,norm_neg,Real.norm_eq_abs,
    abs_of_pos ht,abs_of_nonneg (cubicBesselHeat_nonneg ht)]
  refine h.trans_eq ?_
  calc
    _ = ((k+1).factorial:ℝ)/x^(k+1)*
        ((t^((k+1:ℕ)-4/3:ℝ)/t)*Real.exp (-t)) := by ring
    _ = _ := by rw [hp]

lemma cubicBesselHeatDerivative_integral_bound (k : ℕ) (hk : 1≤k) {x : ℝ} (hx : 0<x) :
    ‖∫ t in Ioi (0:ℝ),cubicBesselHeatDerivative x t‖≤
      ((k+1).factorial:ℝ)/x^(k+1)*Real.Gamma ((k:ℝ)-1/3) := by
  have hkR : (1:ℝ)≤k := by exact_mod_cast hk
  have ha : 0<(k:ℝ)-1/3 := by linarith
  have hefun : (fun t : ℝ => t^((k:ℝ)-4/3)*Real.exp (-t))=
      fun t => t^(((k:ℝ)-1/3)-1)*Real.exp (-1*t) := by
    funext t
    congr 2 <;> ring
  have hi : IntegrableOn (fun t : ℝ => t^((k:ℝ)-4/3)*Real.exp (-t)) (Ioi 0) := by
    rw [hefun]
    exact integrable_laplace_rpow ha (by norm_num : (0:ℝ)<1)
  have hb := integral_mono_ae (cubicBesselHeatDerivative_integrable hx).norm
    (hi.const_mul (((k+1).factorial:ℝ)/x^(k+1))) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact cubicBesselHeatDerivative_power_bound k hx ht)
  have he : (∫ t in Ioi (0:ℝ),t^((k:ℝ)-4/3)*Real.exp (-t))=Real.Gamma ((k:ℝ)-1/3) := by
    rw [hefun,laplace_rpow ha (by norm_num : (0:ℝ)<1)]
    simp
  exact (norm_integral_le_integral_norm _).trans (by
    simpa only [integral_const_mul,he] using hb)

def cubicBesselDerivativePowerConstant (k : ℕ) : ℝ :=
  ((k.factorial:ℝ)/6+((k+1).factorial:ℝ))*Real.Gamma ((k:ℝ)-1/3)

lemma cubicBesselDerivativePowerConstant_pos {k : ℕ} (hk : 1≤k) :
    0<cubicBesselDerivativePowerConstant k := by
  have hkR : (1:ℝ)≤k := by exact_mod_cast hk
  unfold cubicBesselDerivativePowerConstant
  positivity [Real.Gamma_pos_of_pos (show 0<(k:ℝ)-1/3 by linarith)]

theorem cubicBesselKernelDerivative_power_bound (k : ℕ) (hk : 1≤k)
    {x : ℝ} (hx : 0<x) :
    ‖cubicBesselKernelDerivative x‖≤
      cubicBesselDerivativePowerConstant k*x^(-5/6-(k:ℝ)) := by
  have hI : 0≤∫ t in Ioi (0:ℝ),cubicBesselHeat x t :=
    setIntegral_nonneg measurableSet_Ioi (fun _ ht => cubicBesselHeat_nonneg ht)
  have hKI : (∫ t in Ioi (0:ℝ),cubicBesselHeat x t)≤
      (k.factorial:ℝ)*Real.Gamma ((k:ℝ)-1/3)/x^k := by
    apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hx (1/6:ℝ))).mp
    convert cubicBesselKernel_power_bound k hk hx using 1
    · rfl
    · rw [Real.rpow_sub hx,Real.rpow_natCast]
      ring
  have hp1 : x^(-5/6:ℝ)/x^k=x^(-5/6-(k:ℝ)) := by
    rw [Real.rpow_sub hx,Real.rpow_natCast]
  have hp2 : x^(1/6:ℝ)/x^(k+1)=x^(-5/6-(k:ℝ)) := by
    rw [←Real.rpow_natCast,←Real.rpow_sub hx]
    congr 1
    push_cast
    ring
  calc
    _ ≤ ((1/6:ℝ)*x^(-5/6:ℝ))*(∫ t in Ioi (0:ℝ),cubicBesselHeat x t)+
        x^(1/6:ℝ)*‖∫ t in Ioi (0:ℝ),cubicBesselHeatDerivative x t‖ := by
      unfold cubicBesselKernelDerivative
      calc
        _ ≤ ‖((1/6:ℝ)*x^(-5/6:ℝ))*(∫ t in Ioi (0:ℝ),cubicBesselHeat x t)‖+
            ‖x^(1/6:ℝ)*(∫ t in Ioi (0:ℝ),cubicBesselHeatDerivative x t)‖ := norm_add_le _ _
        _ = _ := by
          simp only [norm_mul,Real.norm_of_nonneg (by norm_num : 0≤(1/6:ℝ)),
            Real.norm_of_nonneg (Real.rpow_nonneg hx.le (-5/6:ℝ)),
            Real.norm_of_nonneg hI,Real.norm_of_nonneg (Real.rpow_nonneg hx.le (1/6:ℝ))]
    _ ≤ ((1/6:ℝ)*x^(-5/6:ℝ))*
        ((k.factorial:ℝ)*Real.Gamma ((k:ℝ)-1/3)/x^k)+
        x^(1/6:ℝ)*(((k+1).factorial:ℝ)/x^(k+1)*Real.Gamma ((k:ℝ)-1/3)) :=
      add_le_add (mul_le_mul_of_nonneg_left hKI (by positivity))
        (mul_le_mul_of_nonneg_left (cubicBesselHeatDerivative_integral_bound k hk hx) (by positivity))
    _ = _ := by
      calc
        _ = ((k.factorial:ℝ)/6*Real.Gamma ((k:ℝ)-1/3))*(x^(-5/6:ℝ)/x^k)+
            (((k+1).factorial:ℝ)*Real.Gamma ((k:ℝ)-1/3))*(x^(1/6:ℝ)/x^(k+1)) := by ring
        _ = _ := by rw [hp1,hp2]; unfold cubicBesselDerivativePowerConstant; ring

end CubicFirstMoment

end

end OAI
