import OAI.NumberTheory.CubicMoment.Estimates.CubicBesselDerivativeBounds
import OAI.NumberTheory.CubicMoment.Estimates.CubicWhittakerBounds

namespace OAI

/-! First vertical derivative of the actual cubic Whittaker kernel,
with arbitrary fixed power decay. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaWhittakerDerivative (v : ℝ) : ℂ :=
  ((cubicBesselKernel ((2*Real.pi*v)^2)/2+
    (2*Real.pi*v)^2*cubicBesselKernelDerivative ((2*Real.pi*v)^2):ℝ):ℂ)

theorem cubicThetaWhittaker_hasDerivAt {v : ℝ} (hv : 0<v) :
    HasDerivAt cubicThetaWhittaker (cubicThetaWhittakerDerivative v) v := by
  have hx : 0<(2*Real.pi*v)^2 := by positivity
  have hp := ((hasDerivAt_id v).const_mul (2*Real.pi)).pow 2
  have hb := (cubicBesselKernel_hasDerivAt hx).comp v hp
  have h := ((hasDerivAt_id v).div_const 2).mul hb
  convert h.ofReal_comp using 1
  · funext y
    simp [cubicThetaWhittaker,Function.comp_apply,Pi.mul_apply,Pi.pow_apply]
  · simp only [cubicThetaWhittakerDerivative,Function.comp_apply,Pi.pow_apply,id_eq,
      Nat.cast_ofNat,mul_one]
    push_cast
    ring

def cubicWhittakerDerivativePowerConstant (k : ℕ) : ℝ :=
  (((k.factorial:ℝ)*Real.Gamma ((k:ℝ)-1/3))/2+cubicBesselDerivativePowerConstant k)*
    (2*Real.pi)^(1/3-2*(k:ℝ))

lemma cubicWhittakerDerivativePowerConstant_pos {k : ℕ} (hk : 1≤k) :
    0<cubicWhittakerDerivativePowerConstant k := by
  have hkR : (1:ℝ)≤k := by exact_mod_cast hk
  have hG := Real.Gamma_pos_of_pos (show 0<(k:ℝ)-1/3 by linarith)
  have hD := cubicBesselDerivativePowerConstant_pos hk
  unfold cubicWhittakerDerivativePowerConstant
  positivity

theorem cubicThetaWhittakerDerivative_power_bound (k : ℕ) (hk : 1≤k)
    {v : ℝ} (hv : 0<v) :
    ‖cubicThetaWhittakerDerivative v‖≤
      cubicWhittakerDerivativePowerConstant k*v^(1/3-2*(k:ℝ)) := by
  let x := (2*Real.pi*v)^2
  have hx : 0<x := by dsimp [x]; positivity
  have hK := cubicBesselKernel_power_bound k hk hx
  have hD := cubicBesselKernelDerivative_power_bound k hk hx
  have hp : x*x^(-5/6-(k:ℝ))=x^(1/6-(k:ℝ)) := by
    calc
      _ = x^(1:ℝ)*x^(-5/6-(k:ℝ)) := by rw [Real.rpow_one]
      _ = x^(1+(-5/6-(k:ℝ))) := (Real.rpow_add hx _ _).symm
      _ = _ := by congr 1; ring
  have hs : x^(1/6-(k:ℝ))=(2*Real.pi)^(1/3-2*(k:ℝ))*v^(1/3-2*(k:ℝ)) := by
    dsimp [x]
    rw [←Real.rpow_natCast_mul (by positivity : 0≤2*Real.pi*v)]
    norm_num only [Nat.cast_ofNat]
    rw [show (2:ℝ)*(1/6-(k:ℝ))=1/3-2*(k:ℝ) by ring,
      Real.mul_rpow (by positivity : 0≤2*Real.pi) hv.le]
  calc
    _ ≤ cubicBesselKernel x/2+x*‖cubicBesselKernelDerivative x‖ := by
      change ‖((cubicBesselKernel x/2+x*cubicBesselKernelDerivative x:ℝ):ℂ)‖≤_
      rw [Complex.norm_real]
      calc
        _ ≤ ‖cubicBesselKernel x/2‖+‖x*cubicBesselKernelDerivative x‖ := norm_add_le _ _
        _ = _ := by rw [norm_div,norm_mul,Real.norm_of_nonneg (cubicBesselKernel_nonneg hx.le),
          Real.norm_of_nonneg hx.le]; norm_num
    _ ≤ ((k.factorial:ℝ)*Real.Gamma ((k:ℝ)-1/3)*x^(1/6-(k:ℝ)))/2+
        x*(cubicBesselDerivativePowerConstant k*x^(-5/6-(k:ℝ))) :=
      add_le_add (div_le_div_of_nonneg_right hK (by norm_num))
        (mul_le_mul_of_nonneg_left hD hx.le)
    _ = _ := by
      rw [show x*(cubicBesselDerivativePowerConstant k*x^(-5/6-(k:ℝ)))=
        cubicBesselDerivativePowerConstant k*(x*x^(-5/6-(k:ℝ))) by ring,hp,hs]
      unfold cubicWhittakerDerivativePowerConstant
      ring

end CubicFirstMoment

end

end OAI
