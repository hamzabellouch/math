import OAI.NumberTheory.CubicMoment.Estimates.CubicBesselPowerDecay
import OAI.NumberTheory.CubicMoment.Estimates.CubicBesselContinuity
import OAI.NumberTheory.CubicMoment.Estimates.CubicWhittakerMellin

namespace OAI

/-! Local regularity and explicit majorants of the cubic theta Fourier kernel. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

def cubicWhittakerPowerConstant (k : ℕ) : ℝ :=
  ((k.factorial:ℝ)*Real.Gamma ((k:ℝ)-1/3)/2)*(2*Real.pi)^(1/3-2*(k:ℝ))

lemma cubicWhittakerPowerConstant_pos {k : ℕ} (hk : 1 ≤ k) :
    0 < cubicWhittakerPowerConstant k := by
  have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hg := Real.Gamma_pos_of_pos (show 0 < (k:ℝ)-1/3 by linarith)
  unfold cubicWhittakerPowerConstant
  positivity

lemma cubicThetaWhittaker_norm {v : ℝ} (hv : 0 < v) :
    ‖cubicThetaWhittaker v‖ = v/2*cubicBesselKernel ((2*Real.pi*v)^2) := by
  simp only [cubicThetaWhittaker,norm_mul,norm_div,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos hv]
  rw [abs_of_nonneg (cubicBesselKernel_nonneg (sq_nonneg _))]
  norm_num

lemma cubicThetaWhittaker_continuousAt {v : ℝ} (hv : 0 < v) :
    ContinuousAt cubicThetaWhittaker v := by
  have hx : 0 < (2*Real.pi*v)^2 := by positivity
  have hk : ContinuousAt cubicBesselKernel ((2*Real.pi*v)^2) :=
    cubicBesselKernel_continuousOn.continuousAt (isOpen_Ioi.mem_nhds hx)
  have hc : ContinuousAt (fun w : ℝ => (2*Real.pi*w)^2) v := by fun_prop
  have hi : ContinuousAt (fun w : ℝ => (cubicBesselKernel ((2*Real.pi*w)^2):ℂ)) v :=
    Complex.continuous_ofReal.continuousAt.comp (hk.comp (f := fun w : ℝ => (2*Real.pi*w)^2) hc)
  exact (Complex.continuous_ofReal.continuousAt.div_const 2).mul hi

/-- Every fixed power majorant is available on the full positive axis. -/
theorem cubicThetaWhittaker_power_bound (k : ℕ) (hk : 1 ≤ k) {v : ℝ} (hv : 0 < v) :
    ‖cubicThetaWhittaker v‖ ≤ cubicWhittakerPowerConstant k*v^(4/3-2*(k:ℝ)) := by
  rw [cubicThetaWhittaker_norm hv]
  apply (mul_le_mul_of_nonneg_left
    (cubicBesselKernel_power_bound k hk (show 0 < (2*Real.pi*v)^2 by positivity))
    (by positivity : 0 ≤ v/2)).trans_eq
  have hp : ((2*Real.pi*v)^2)^(1/6-(k:ℝ)) =
      (2*Real.pi)^(1/3-2*(k:ℝ))*v^(1/3-2*(k:ℝ)) := by
    rw [←Real.rpow_natCast_mul (by positivity : 0 ≤ 2*Real.pi*v)]
    norm_num only [Nat.cast_ofNat]
    rw [show (2:ℝ)*(1/6-(k:ℝ))=1/3-2*(k:ℝ) by ring,
      Real.mul_rpow (by positivity : 0 ≤ 2*Real.pi) hv.le]
  rw [hp]
  have hvp : v*v^(1/3-2*(k:ℝ)) = v^(4/3-2*(k:ℝ)) := by
    calc
      _ = v^(1:ℝ)*v^(1/3-2*(k:ℝ)) := by rw [Real.rpow_one]
      _ = v^(1+(1/3-2*(k:ℝ))) := (Real.rpow_add hv _ _).symm
      _ = _ := by congr 1; ring
  unfold cubicWhittakerPowerConstant
  calc
    _ = (((k.factorial:ℝ)*Real.Gamma ((k:ℝ)-1/3)/2)*(2*Real.pi)^(1/3-2*(k:ℝ)))*
        (v*v^(1/3-2*(k:ℝ))) := by ring
    _ = _ := by rw [hvp]

end CubicFirstMoment

end

end OAI
