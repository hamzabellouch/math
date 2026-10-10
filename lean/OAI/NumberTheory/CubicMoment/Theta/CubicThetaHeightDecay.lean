import OAI.NumberTheory.CubicMoment.Theta.CubicThetaContinuity

namespace OAI

/-! Arbitrary power decay at the infinite cusp, derived from the actual
Whittaker integral and a single absolutely convergent lattice majorant. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma cubicThetaFrequency_rpow {n : Eisenstein} (hn : n ≠ 0) (s : ℝ) :
    ‖cubicThetaFrequency n‖^s = 81^(-s/2)*norm n^(s/2) := by
  have hp := cubicThetaFrequency_pos hn
  have hN := norm_pos_of_ne_zero hn
  calc
    _ = (‖cubicThetaFrequency n‖^2)^(s/2) := by
      rw [←Real.rpow_natCast_mul hp.le]
      congr 1
      push_cast
      ring
    _ = (norm n/81)^(s/2) := by rw [cubicThetaFrequency_sq]
    _ = norm n^(s/2)/81^(s/2) := Real.div_rpow hN.le (by norm_num) _
    _ = 81^(-s/2)*norm n^(s/2) := by
      rw [neg_div,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 81)]
      ring

lemma cubicThetaSeriesTerm_height_bound (k : ℕ) (hk : 3 ≤ k)
    {a : Eisenstein → ℂ} {C v : ℝ} (hC : 0 ≤ C)
    (ha : ∀ n : Eisenstein, n ≠ 0 → ‖a n‖ ≤ C*norm n)
    (hv : 0 < v) (z : ℂ) (n : Eisenstein) :
    ‖cubicThetaSeriesTerm a z v n‖ ≤
      (C*cubicWhittakerPowerConstant k*81^((k:ℝ)-2/3)*v^(4/3-2*(k:ℝ)))*
        norm n^(-4/3:ℝ) := by
  have hkp : 1 ≤ k := by omega
  have hkR : (3:ℝ) ≤ k := by exact_mod_cast hk
  have hK := (cubicWhittakerPowerConstant_pos hkp).le
  by_cases hn : n = 0
  · simp only [cubicThetaSeriesTerm,hn,ite_true,norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC hK) (by positivity))
      (by positivity)) (Real.rpow_nonneg (norm_nonneg _) _)
  · simp only [cubicThetaSeriesTerm,hn,ite_false,norm_mul,Circle.norm_coe,mul_one]
    have hN := norm_pos_of_ne_zero hn
    have hw := cubicThetaWhittaker_power_bound k hkp (mul_pos (cubicThetaFrequency_pos hn) hv)
    rw [Real.mul_rpow (cubicThetaFrequency_pos hn).le hv.le,cubicThetaFrequency_rpow hn] at hw
    have he1 : -(4/3-2*(k:ℝ))/2 = (k:ℝ)-2/3 := by ring
    have he2 : (4/3-2*(k:ℝ))/2 = 2/3-(k:ℝ) := by ring
    rw [he1,he2] at hw
    have hprod : norm n*norm n^(2/3-(k:ℝ)) = norm n^(5/3-(k:ℝ)) := by
      calc
        _ = norm n^(1:ℝ)*norm n^(2/3-(k:ℝ)) := by rw [Real.rpow_one]
        _ = norm n^(1+(2/3-(k:ℝ))) := (Real.rpow_add hN _ _).symm
        _ = _ := by congr 1; ring
    have hpow : norm n^(5/3-(k:ℝ)) ≤ norm n^(-4/3:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (one_le_norm hn) (by linarith)
    calc
      _ ≤ (C*norm n)*(cubicWhittakerPowerConstant k*
          (81^((k:ℝ)-2/3)*norm n^(2/3-(k:ℝ))*v^(4/3-2*(k:ℝ)))) :=
        mul_le_mul (ha n hn) hw (_root_.norm_nonneg _) (mul_nonneg hC hN.le)
      _ = (C*cubicWhittakerPowerConstant k*81^((k:ℝ)-2/3)*v^(4/3-2*(k:ℝ)))*
          norm n^(5/3-(k:ℝ)) := by
        calc
          _ = (C*cubicWhittakerPowerConstant k*81^((k:ℝ)-2/3)*v^(4/3-2*(k:ℝ)))*
            (norm n*norm n^(2/3-(k:ℝ))) := by ring
          _ = _ := by rw [hprod]
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)

/-- The full nonconstant cusp expansion decreases faster than any prescribed
power, uniformly in horizontal position. -/
theorem cubicThetaNonconstant_height_bound (k : ℕ) (hk : 3 ≤ k)
    {a : Eisenstein → ℂ} {C v : ℝ} (hC : 0 ≤ C)
    (ha : ∀ n : Eisenstein, n ≠ 0 → ‖a n‖ ≤ C*norm n)
    (hv : 0 < v) (z : ℂ) :
    ‖cubicThetaNonconstant a (z,v)‖ ≤
      (C*cubicWhittakerPowerConstant k*81^((k:ℝ)-2/3)*
        (∑' n : Eisenstein, norm n^(-4/3:ℝ)))*v^(4/3-2*(k:ℝ)) := by
  have hs := cubicThetaSeries_summable hC ha hv z
  let D := C*cubicWhittakerPowerConstant k*81^((k:ℝ)-2/3)*v^(4/3-2*(k:ℝ))
  have hmajor : Summable (fun n : Eisenstein => D*norm n^(-4/3:ℝ)) := by
    simpa only [neg_div] using
      (summable_eisenstein_norm_rpow (by norm_num : (1:ℝ) < 4/3)).mul_left D
  calc
    _ ≤ ∑' n : Eisenstein, ‖cubicThetaSeriesTerm a z v n‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' n : Eisenstein, D*norm n^(-4/3:ℝ) :=
      Summable.tsum_le_tsum (cubicThetaSeriesTerm_height_bound k hk hC ha hv z) hs.norm hmajor
    _ = _ := by rw [tsum_mul_left]; dsimp [D]; ring

end CubicFirstMoment

end

end OAI
