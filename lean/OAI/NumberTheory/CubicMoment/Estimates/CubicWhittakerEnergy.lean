import OAI.NumberTheory.CubicMoment.Estimates.CubicWhittakerExponential
import OAI.NumberTheory.CubicMoment.Estimates.CubicWhittakerConvergence

namespace OAI

/-! Absolute squared Mellin masses for the fixed cubic Whittaker kernel. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma cubicThetaWhittaker_sq_bound {v : ℝ} (hv : 0 < v) :
    ‖cubicThetaWhittaker v‖^2 ≤ cubicWhittakerExpConstant^2 *
      v^(4/3:ℝ) * Real.exp (-(4*Real.pi*v)) := by
  apply (pow_le_pow_left₀ (_root_.norm_nonneg _) (cubicThetaWhittaker_exponential_bound hv) 2).trans_eq
  have hp : (v^(2/3:ℝ))^2=v^(4/3:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hv.le]
    congr 1
    norm_num
  have he : (Real.exp (-(2*Real.pi*v)))^2=Real.exp (-(4*Real.pi*v)) := by
    rw [←Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [mul_pow,mul_pow,hp,he]

def cubicWhittakerEnergyMass (σ : ℝ) : ℝ :=
  ∫ v in Ioi (0:ℝ), v^(2*σ-1)*‖cubicThetaWhittaker v‖^2

lemma cubicWhittakerEnergy_integrable {σ : ℝ} (hσ : 0 ≤ σ) :
    IntegrableOn (fun v : ℝ => v^(2*σ-1)*‖cubicThetaWhittaker v‖^2) (Ioi 0) := by
  have hc : ContinuousOn (fun v : ℝ => v^(2*σ-1)*‖cubicThetaWhittaker v‖^2) (Ioi 0) := by
    intro v hv
    have hW := cubicThetaWhittaker_continuousAt hv
    have hp : ContinuousAt (fun v : ℝ => v^(2*σ-1)) v := by
      exact Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt hv))
    exact (hp.mul (hW.norm.pow 2)).continuousWithinAt
  have hi := (integrable_laplace_rpow (by linarith : 0 < 2*σ+4/3)
    (by positivity : 0 < 4*Real.pi)).const_mul (cubicWhittakerExpConstant^2)
  apply hi.mono' (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hv.le _) (sq_nonneg _))]
  apply (mul_le_mul_of_nonneg_left (cubicThetaWhittaker_sq_bound hv)
    (Real.rpow_nonneg hv.le _)).trans_eq
  rw [show v^(2*σ-1)*(cubicWhittakerExpConstant^2*v^(4/3:ℝ)*
      Real.exp (-(4*Real.pi*v))) = cubicWhittakerExpConstant^2*
      (v^(2*σ-1)*v^(4/3:ℝ))*Real.exp (-(4*Real.pi*v)) by ring,
    ←Real.rpow_add hv]
  rw [show 2*σ-1+4/3=2*σ+4/3-1 by ring,
    show -(4*Real.pi*v)=-(4*Real.pi)*v by ring]
  ring

lemma cubicWhittakerEnergyMass_nonneg (σ : ℝ) : 0 ≤ cubicWhittakerEnergyMass σ := by
  apply setIntegral_nonneg measurableSet_Ioi
  intro v hv
  exact mul_nonneg (Real.rpow_nonneg hv.le _) (sq_nonneg _)

lemma cubicWhittakerEnergy_mass_scale (σ : ℝ) {r : ℝ} (hr : 0 < r) :
    (∫ v in Ioi (0:ℝ), v^(2*σ-1)*‖cubicThetaWhittaker (r*v)‖^2) =
      r^(-2*σ)*cubicWhittakerEnergyMass σ := by
  have hcancel : r^(1-2*σ)*r^(2*σ-1)=1 := by
    rw [←Real.rpow_add hr]
    ring_nf
    exact Real.rpow_zero _
  have he : (∫ v in Ioi (0:ℝ), v^(2*σ-1)*‖cubicThetaWhittaker (r*v)‖^2) =
      r^(1-2*σ)*(∫ v in Ioi (0:ℝ), (r*v)^(2*σ-1)*‖cubicThetaWhittaker (r*v)‖^2) := by
    rw [←integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    dsimp only
    rw [Real.mul_rpow hr.le hv.le]
    simp only [←mul_assoc,hcancel,one_mul]
  rw [he,integral_comp_mul_left_Ioi
    (fun v : ℝ => v^(2*σ-1)*‖cubicThetaWhittaker v‖^2) 0 hr,mul_zero]
  simp only [smul_eq_mul]
  have hp : r^(1-2*σ)*r⁻¹=r^(-2*σ) := by
    rw [←Real.rpow_neg_one,←Real.rpow_add hr]
    congr 1
    ring
  rw [←mul_assoc,hp]
  rfl

lemma cubicWhittakerEnergy_scaled_integrable {σ : ℝ} (hσ : 0 ≤ σ)
    {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun v : ℝ => v^(2*σ-1)*‖cubicThetaWhittaker (r*v)‖^2) (Ioi 0) := by
  have h := (integrableOn_Ioi_comp_mul_left_iff
    (fun v : ℝ => v^(2*σ-1)*‖cubicThetaWhittaker v‖^2) 0 hr).mpr
    (by simpa only [mul_zero] using cubicWhittakerEnergy_integrable hσ)
  have hi := h.const_mul (r^(1-2*σ))
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  rw [Real.mul_rpow hr.le hv.le]
  have hp : r^(1-2*σ)*r^(2*σ-1)=1 := by
    rw [←Real.rpow_add hr]
    ring_nf
    exact Real.rpow_zero _
  rw [←mul_assoc,←mul_assoc,hp,one_mul]


end CubicFirstMoment

end

end OAI
