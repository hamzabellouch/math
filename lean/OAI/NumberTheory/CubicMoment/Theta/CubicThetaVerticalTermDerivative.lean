import OAI.NumberTheory.CubicMoment.Estimates.CubicWhittakerDerivative
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAngularConvergence

namespace OAI

/-! Actual first vertical derivatives of the fixed-angular Fourier terms. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaSeriesTermVertical (a : Eisenstein → ℂ) (z : ℂ) (v : ℝ) (n : Eisenstein) : ℂ :=
  if n=0 then 0 else a n*cubicThetaWhittakerDerivative (‖cubicThetaFrequency n‖*v)*
    (‖cubicThetaFrequency n‖:ℂ)*(Real.fourierChar (tracePair (cubicThetaFrequency n) z):ℂ)

theorem cubicThetaSeriesTerm_vertical_hasDerivAt (a : Eisenstein → ℂ)
    (z : ℂ) {v : ℝ} (hv : 0<v) (n : Eisenstein) :
    HasDerivAt (fun y => cubicThetaSeriesTerm a z y n) (cubicThetaSeriesTermVertical a z v n) v := by
  by_cases hn : n=0
  · simp only [cubicThetaSeriesTerm,cubicThetaSeriesTermVertical,hn,ite_true]
    exact hasDerivAt_const v 0
  have hr := cubicThetaFrequency_pos hn
  have h := ((cubicThetaWhittaker_hasDerivAt (mul_pos hr hv)).scomp v
    ((hasDerivAt_id v).const_mul ‖cubicThetaFrequency n‖)).const_mul (a n)
  have h' := h.mul_const (Real.fourierChar (tracePair (cubicThetaFrequency n) z):ℂ)
  convert h' using 1
  · funext y
    simp only [cubicThetaSeriesTerm,hn,ite_false,Function.comp_apply]
  · simp only [cubicThetaSeriesTermVertical,hn,ite_false,Complex.real_smul,mul_one]
    ring

lemma cubicThetaVertical_kernel_bound (k : ℕ) {n : Eisenstein} (hn : n≠0)
    {v : ℝ} (hv : 0<v) :
    ‖cubicThetaFrequency n‖^(k+1)*
        ‖cubicThetaWhittakerDerivative (‖cubicThetaFrequency n‖*v)‖≤
      (cubicWhittakerDerivativePowerConstant (k+3)*(9:ℝ)^k*81^(7/3:ℝ))*
        v^(1/3-2*((k:ℝ)+3))*norm n^(-7/3:ℝ) := by
  have hr := cubicThetaFrequency_pos hn
  have hD := (cubicWhittakerDerivativePowerConstant_pos (by omega : 1≤k+3)).le
  have hw := cubicThetaWhittakerDerivative_power_bound (k+3) (by omega) (mul_pos hr hv)
  simp only [Nat.cast_add,Nat.cast_ofNat] at hw
  rw [Real.mul_rpow hr.le hv.le] at hw
  have hp : ‖cubicThetaFrequency n‖^(k+1)*‖cubicThetaFrequency n‖^(1/3-2*((k:ℝ)+3))=
      ‖cubicThetaFrequency n‖^(-(k:ℝ))*‖cubicThetaFrequency n‖^(-14/3:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_add hr,←Real.rpow_add hr]
    congr 1
    push_cast
    ring
  calc
    _ ≤ ‖cubicThetaFrequency n‖^(k+1)*(cubicWhittakerDerivativePowerConstant (k+3)*
        (‖cubicThetaFrequency n‖^(1/3-2*((k:ℝ)+3))*v^(1/3-2*((k:ℝ)+3)))) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    _ = cubicWhittakerDerivativePowerConstant (k+3)*v^(1/3-2*((k:ℝ)+3))*
        (‖cubicThetaFrequency n‖^(-(k:ℝ))*‖cubicThetaFrequency n‖^(-14/3:ℝ)) := by
      calc
        _ = cubicWhittakerDerivativePowerConstant (k+3)*v^(1/3-2*((k:ℝ)+3))*
            (‖cubicThetaFrequency n‖^(k+1)*‖cubicThetaFrequency n‖^(1/3-2*((k:ℝ)+3))) := by ring
        _ = _ := by rw [hp]
    _ ≤ cubicWhittakerDerivativePowerConstant (k+3)*v^(1/3-2*((k:ℝ)+3))*
        ((9:ℝ)^k*‖cubicThetaFrequency n‖^(-14/3:ℝ)) := by
      gcongr
      exact cubicThetaFrequency_inverse_pow hn k
    _ = _ := by rw [cubicThetaFrequency_power hn]; ring

lemma cubicThetaAngular_vertical_term_bound {a : Eisenstein → ℂ} {C v : ℝ}
    (hC : 0≤C) (ha : ∀ n : Eisenstein,n≠0 → ‖a n‖≤C*norm n)
    (ℓ : ℤ) (hv : 0<v) (z : ℂ) (n : Eisenstein) :
    ‖cubicThetaSeriesTermVertical (cubicThetaAngularCoefficient a ℓ) z v n‖≤
      (C*cubicWhittakerDerivativePowerConstant (ℓ.natAbs+3)*(9:ℝ)^ℓ.natAbs*81^(7/3:ℝ)*
        v^(1/3-2*((ℓ.natAbs:ℝ)+3)))*norm n^(-4/3:ℝ) := by
  by_cases hn : n=0
  · simp only [cubicThetaSeriesTermVertical,hn,ite_true,norm_zero]
    norm_num [norm]
  have hN := norm_pos_of_ne_zero hn
  simp only [cubicThetaSeriesTermVertical,hn,ite_false,norm_mul,Circle.norm_coe,mul_one,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (_root_.norm_nonneg _),
    cubicThetaAngularCoefficient_norm ℓ hn]
  have hp : norm n*norm n^(-7/3:ℝ)=norm n^(-4/3:ℝ) := by
    calc
      _ = norm n^(1:ℝ)*norm n^(-7/3:ℝ) := by rw [Real.rpow_one]
      _ = norm n^(1+(-7/3:ℝ)) := (Real.rpow_add hN _ _).symm
      _ = _ := by congr 1; ring
  calc
    _ = ‖a n‖*(‖cubicThetaFrequency n‖^(ℓ.natAbs+1)*
        ‖cubicThetaWhittakerDerivative (‖cubicThetaFrequency n‖*v)‖) := by rw [pow_succ]; ring
    _ ≤ (C*norm n)*((cubicWhittakerDerivativePowerConstant (ℓ.natAbs+3)*
        (9:ℝ)^ℓ.natAbs*81^(7/3:ℝ))*v^(1/3-2*((ℓ.natAbs:ℝ)+3))*norm n^(-7/3:ℝ)) :=
      mul_le_mul (ha n hn) (cubicThetaVertical_kernel_bound ℓ.natAbs hn hv)
        (mul_nonneg (by positivity) (_root_.norm_nonneg _)) (mul_nonneg hC hN.le)
    _ = _ := by
      calc
        _ = (C*cubicWhittakerDerivativePowerConstant (ℓ.natAbs+3)*
            (9:ℝ)^ℓ.natAbs*81^(7/3:ℝ)*v^(1/3-2*((ℓ.natAbs:ℝ)+3)))*
            (norm n*norm n^(-7/3:ℝ)) := by ring
        _ = _ := by rw [hp]

end CubicFirstMoment

end

end OAI
