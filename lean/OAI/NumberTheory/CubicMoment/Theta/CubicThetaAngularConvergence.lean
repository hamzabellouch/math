import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAngularPowers
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaExponential

namespace OAI

/-! Absolute convergence of the fixed-angular frequency derivatives.
An explicit summable lattice majorant absorbs every fixed derivative order. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaFrequency_inverse_pow {n : Eisenstein} (hn : n ≠ 0) (k : ℕ) :
    ‖cubicThetaFrequency n‖^(-(k:ℝ)) ≤ (9:ℝ)^k := by
  calc
    _ ≤ (1/9:ℝ)^(-(k:ℝ)) := Real.rpow_le_rpow_of_nonpos (by norm_num)
      (cubicThetaFrequency_lower hn) (neg_nonpos.mpr (Nat.cast_nonneg k))
    _ = (9:ℝ)^k := by
      rw [Real.rpow_neg_eq_inv_rpow]
      norm_num only [one_div,inv_inv]
      rw [Real.rpow_natCast]

lemma cubicThetaAngular_kernel_bound (k : ℕ) {n : Eisenstein} (hn : n ≠ 0)
    {v : ℝ} (hv : 0 < v) :
    ‖cubicThetaFrequency n‖^k*‖cubicThetaWhittaker (‖cubicThetaFrequency n‖*v)‖ ≤
      (cubicWhittakerPowerConstant (k+3)*(9:ℝ)^k*81^(7/3:ℝ))*
        v^(4/3-2*((k:ℝ)+3))*norm n^(-7/3:ℝ) := by
  have hr := cubicThetaFrequency_pos hn
  have hK := (cubicWhittakerPowerConstant_pos (by omega : 1 ≤ k+3)).le
  have hw := cubicThetaWhittaker_power_bound (k+3) (by omega) (mul_pos hr hv)
  simp only [Nat.cast_add,Nat.cast_ofNat] at hw
  rw [Real.mul_rpow hr.le hv.le] at hw
  have hp : ‖cubicThetaFrequency n‖^k*‖cubicThetaFrequency n‖^(4/3-2*((k:ℝ)+3)) =
      ‖cubicThetaFrequency n‖^(-(k:ℝ))*‖cubicThetaFrequency n‖^(-14/3:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_add hr,←Real.rpow_add hr]
    congr 1
    ring
  calc
    _ ≤ ‖cubicThetaFrequency n‖^k*(cubicWhittakerPowerConstant (k+3)*
        (‖cubicThetaFrequency n‖^(4/3-2*((k:ℝ)+3))*v^(4/3-2*((k:ℝ)+3)))) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    _ = cubicWhittakerPowerConstant (k+3)*v^(4/3-2*((k:ℝ)+3))*
        (‖cubicThetaFrequency n‖^(-(k:ℝ))*‖cubicThetaFrequency n‖^(-14/3:ℝ)) := by
      calc
        _ = cubicWhittakerPowerConstant (k+3)*v^(4/3-2*((k:ℝ)+3))*
            (‖cubicThetaFrequency n‖^k*‖cubicThetaFrequency n‖^(4/3-2*((k:ℝ)+3))) := by ring
        _ = _ := by rw [hp]
    _ ≤ cubicWhittakerPowerConstant (k+3)*v^(4/3-2*((k:ℝ)+3))*
        ((9:ℝ)^k*‖cubicThetaFrequency n‖^(-14/3:ℝ)) := by
      gcongr
      exact cubicThetaFrequency_inverse_pow hn k
    _ = _ := by rw [cubicThetaFrequency_power hn]; ring

lemma cubicThetaAngular_term_bound {a : Eisenstein → ℂ} {C v : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, n ≠ 0 → ‖a n‖ ≤ C*norm n)
    (ℓ : ℤ) (hv : 0 < v) (z : ℂ) (n : Eisenstein) :
    ‖cubicThetaSeriesTerm (cubicThetaAngularCoefficient a ℓ) z v n‖ ≤
      (C*cubicWhittakerPowerConstant (ℓ.natAbs+3)*(9:ℝ)^ℓ.natAbs*81^(7/3:ℝ)*
        v^(4/3-2*((ℓ.natAbs:ℝ)+3)))*norm n^(-4/3:ℝ) := by
  have hK := (cubicWhittakerPowerConstant_pos (by omega : 1 ≤ ℓ.natAbs+3)).le
  by_cases hn : n = 0
  · simp only [cubicThetaSeriesTerm,hn,ite_true,norm_zero]
    norm_num [norm]
  · have hN := norm_pos_of_ne_zero hn
    simp only [cubicThetaSeriesTerm,hn,ite_false,norm_mul,Circle.norm_coe,mul_one,
      cubicThetaAngularCoefficient_norm ℓ hn]
    have hp : norm n*norm n^(-7/3:ℝ) = norm n^(-4/3:ℝ) := by
      calc
        _ = norm n^(1:ℝ)*norm n^(-7/3:ℝ) := by rw [Real.rpow_one]
        _ = norm n^(1+(-7/3:ℝ)) := (Real.rpow_add hN _ _).symm
        _ = _ := by congr 1; ring
    calc
      _ = ‖a n‖*(‖cubicThetaFrequency n‖^ℓ.natAbs*
          ‖cubicThetaWhittaker (‖cubicThetaFrequency n‖*v)‖) := by ring
      _ ≤ (C*norm n)*((cubicWhittakerPowerConstant (ℓ.natAbs+3)*(9:ℝ)^ℓ.natAbs*81^(7/3:ℝ))*
          v^(4/3-2*((ℓ.natAbs:ℝ)+3))*norm n^(-7/3:ℝ)) :=
        mul_le_mul (ha n hn) (cubicThetaAngular_kernel_bound ℓ.natAbs hn hv)
          (mul_nonneg (by positivity) (_root_.norm_nonneg _)) (mul_nonneg hC hN.le)
      _ = _ := by
        calc
          _ = (C*cubicWhittakerPowerConstant (ℓ.natAbs+3)*(9:ℝ)^ℓ.natAbs*81^(7/3:ℝ)*
              v^(4/3-2*((ℓ.natAbs:ℝ)+3)))*(norm n*norm n^(-7/3:ℝ)) := by ring
          _ = _ := by rw [hp]

/-- Every fixed signed angular derivative is an absolutely convergent
Fourier series at each positive height. -/
theorem cubicThetaAngular_summable {a : Eisenstein → ℂ} {C v : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, n ≠ 0 → ‖a n‖ ≤ C*norm n)
    (ℓ : ℤ) (hv : 0 < v) (z : ℂ) :
    Summable (cubicThetaSeriesTerm (cubicThetaAngularCoefficient a ℓ) z v) := by
  apply ((summable_eisenstein_norm_rpow (by norm_num : (1:ℝ) < 4/3)).mul_left
    (C*cubicWhittakerPowerConstant (ℓ.natAbs+3)*(9:ℝ)^ℓ.natAbs*81^(7/3:ℝ)*
      v^(4/3-2*((ℓ.natAbs:ℝ)+3)))).of_norm_bounded
  intro n
  simpa only [neg_div] using cubicThetaAngular_term_bound hC ha ℓ hv z n

end CubicFirstMoment

end

end OAI
