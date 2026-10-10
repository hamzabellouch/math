import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeZeroMode

namespace OAI

/-! The spherical multiplier of the actual finite cubed-prime operator,
including its critical value on both height exponents 4/3 and 2/3. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeHeight_rpow (r v σ : ℝ) (hr : 0<r) (hv : 0<v) :
    (r^3*v)^σ+r^6*((1/r^3)*v)^σ=
      (r^(3*σ)+r^(6-3*σ))*v^σ := by
  have h3 : (r^3)^σ=r^(3*σ) := by
    rw [←Real.rpow_natCast r 3,←Real.rpow_mul hr.le]
    norm_num
  have h6 : r^6=r^(6:ℝ) := (Real.rpow_natCast r 6).symm
  rw [Real.mul_rpow (by positivity) hv.le,Real.mul_rpow (by positivity) hv.le,h3,
    one_div,Real.inv_rpow (by positivity),h3,←Real.rpow_neg hr.le]
  rw [h6]
  have he : r^(6:ℝ)*r^(-(3*σ))=r^(6-3*σ) := by
    rw [←Real.rpow_add hr]
    congr 1
  calc
    _ = (r^(3*σ)+r^(6:ℝ)*r^(-(3*σ)))*v^σ := by ring
    _ = _ := by rw [he]

lemma cubicThetaPrimeCube_norm_power {p : Eisenstein} :
    norm (p^3)=‖(p:ℂ)‖^6 := by
  change Complex.normSq ((p^3:Eisenstein):ℂ)=_
  rw [Subalgebra.coe_pow,Complex.normSq_eq_norm_sq,norm_pow]
  ring

theorem cubicThetaPrimeCubeFunctionOperator_heightPower {p : Eisenstein}
    (hp : primaryPrime p) (σ : ℝ) (x : CubicThetaPoint) :
    cubicThetaPrimeCubeFunctionOperator hp (fun y => ((y.val.2^σ:ℝ):ℂ)) x=
      ((‖(p:ℂ)‖^(3*σ)+‖(p:ℂ)‖^(6-3*σ):ℝ):ℂ)*((x.val.2^σ:ℝ):ℂ) := by
  have he := cubicThetaPrimeCubeFunctionOperator_height hp (fun v : ℝ => ((v^σ:ℝ):ℂ)) x
  rw [cubicThetaPrimeCube_norm_power] at he
  rw [he]
  have hr : 0<‖(p:ℂ)‖ := norm_pos_iff.mpr (fun hz => hp.2.ne_zero (Subtype.ext hz))
  exact_mod_cast cubicThetaPrimeCubeHeight_rpow ‖(p:ℂ)‖ x.val.2 σ hr x.property

theorem cubicThetaPrimeCubeFunctionOperator_criticalHeight {p : Eisenstein}
    (hp : primaryPrime p) (x : CubicThetaPoint) :
    cubicThetaPrimeCubeFunctionOperator hp (fun y => ((y.val.2^(4/3:ℝ):ℝ):ℂ)) x=
      ((norm p)^2+norm p:ℂ)*((x.val.2^(4/3:ℝ):ℝ):ℂ) := by
  rw [cubicThetaPrimeCubeFunctionOperator_heightPower]
  have he : ‖(p:ℂ)‖^(3*(4/3:ℝ))+‖(p:ℂ)‖^(6-3*(4/3:ℝ))=(norm p)^2+norm p := by
    norm_num
    change ‖(p:ℂ)‖^4+‖(p:ℂ)‖^2=(Complex.normSq (p:ℂ))^2+Complex.normSq (p:ℂ)
    rw [Complex.normSq_eq_norm_sq]
    ring
  rw [he]
  push_cast
  rfl

theorem cubicThetaPrimeCubeFunctionOperator_residualHeight {p : Eisenstein}
    (hp : primaryPrime p) (x : CubicThetaPoint) :
    cubicThetaPrimeCubeFunctionOperator hp (fun y => ((y.val.2^(2/3:ℝ):ℝ):ℂ)) x=
      ((norm p)^2+norm p:ℂ)*((x.val.2^(2/3:ℝ):ℝ):ℂ) := by
  rw [cubicThetaPrimeCubeFunctionOperator_heightPower]
  have he : ‖(p:ℂ)‖^(3*(2/3:ℝ))+‖(p:ℂ)‖^(6-3*(2/3:ℝ))=(norm p)^2+norm p := by
    norm_num
    change ‖(p:ℂ)‖^2+‖(p:ℂ)‖^4=(Complex.normSq (p:ℂ))^2+Complex.normSq (p:ℂ)
    rw [Complex.normSq_eq_norm_sq]
    ring
  rw [he]
  push_cast
  rfl

end CubicFirstMoment

end

end OAI
