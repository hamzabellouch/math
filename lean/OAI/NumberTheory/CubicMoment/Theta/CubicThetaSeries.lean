import OAI.NumberTheory.CubicMoment.Estimates.CubicWhittakerBounds
import OAI.NumberTheory.CubicMoment.Estimates.SchwartzLattice

namespace OAI

/-! Absolute convergence of the cubic theta Fourier expansion on its actual
common cusp frequency lattice lambda^{-4} Z[omega]. The coefficient here includes the
factor 1/|mu| when the Whittaker function is evaluated at |mu|v. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaFrequency (n : Eisenstein) : ℂ := (n:ℂ)/traceLambda^4

def cubicThetaSeriesTerm (a : Eisenstein → ℂ) (z : ℂ) (v : ℝ) (n : Eisenstein) : ℂ :=
  if n = 0 then 0 else a n*cubicThetaWhittaker (‖cubicThetaFrequency n‖*v)*
    (Real.fourierChar (tracePair (cubicThetaFrequency n) z) : ℂ)

lemma cubicThetaFrequency_pos {n : Eisenstein} (hn : n ≠ 0) :
    0 < ‖cubicThetaFrequency n‖ := by
  apply norm_pos_iff.mpr
  exact div_ne_zero (fun h => hn (Subtype.ext h)) (pow_ne_zero 4 traceLambda_ne_zero)

lemma cubicThetaFrequency_sq (n : Eisenstein) :
    ‖cubicThetaFrequency n‖^2 = norm n/81 := by
  rw [←Complex.normSq_eq_norm_sq]
  unfold cubicThetaFrequency
  rw [Complex.normSq_div,map_pow,traceLambda_normSq]
  norm_num
  rfl

lemma cubicThetaFrequency_power {n : Eisenstein} (hn : n ≠ 0) :
    ‖cubicThetaFrequency n‖^(-14/3:ℝ) = 81^(7/3:ℝ)*norm n^(-7/3:ℝ) := by
  have hp := cubicThetaFrequency_pos hn
  have hN := norm_pos_of_ne_zero hn
  calc
    _ = (‖cubicThetaFrequency n‖^2)^(-7/3:ℝ) := by
      rw [←Real.rpow_natCast_mul hp.le]
      norm_num
    _ = (norm n/81)^(-7/3:ℝ) := by rw [cubicThetaFrequency_sq]
    _ = norm n^(-7/3:ℝ) / 81^(-7/3:ℝ) :=
      Real.div_rpow hN.le (by norm_num) _
    _ = 81^(7/3:ℝ)*norm n^(-7/3:ℝ) := by
      have he : ((81:ℝ)^(-7/3:ℝ))⁻¹ = 81^(7/3:ℝ) := by
        rw [←Real.rpow_neg (by norm_num : (0:ℝ) ≤ 81)]
        congr 1
        ring
      calc
        _ = norm n^(-7/3:ℝ)*((81:ℝ)^(-7/3:ℝ))⁻¹ := div_eq_mul_inv _ _
        _ = _ := by rw [he]; ring

lemma cubicThetaWhittaker_frequency_bound {n : Eisenstein} (hn : n ≠ 0)
    {v : ℝ} (hv : 0 < v) :
    ‖cubicThetaWhittaker (‖cubicThetaFrequency n‖*v)‖ ≤
      (cubicWhittakerPowerConstant 3*81^(7/3:ℝ))*v^(-14/3:ℝ)*norm n^(-7/3:ℝ) := by
  have hb := cubicThetaWhittaker_power_bound 3 (by omega)
    (mul_pos (cubicThetaFrequency_pos hn) hv)
  norm_num only [Nat.cast_ofNat] at hb
  rw [show -(14/3:ℝ) = -14/3 by ring,
    Real.mul_rpow (cubicThetaFrequency_pos hn).le hv.le,cubicThetaFrequency_power hn] at hb
  convert hb using 1; ring

lemma cubicThetaSeriesTerm_bound {a : Eisenstein → ℂ} {C v : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, n ≠ 0 → ‖a n‖ ≤ C*norm n)
    (hv : 0 < v) (z : ℂ) (n : Eisenstein) :
    ‖cubicThetaSeriesTerm a z v n‖ ≤
      (C*cubicWhittakerPowerConstant 3*81^(7/3:ℝ)*v^(-14/3:ℝ))*norm n^(-4/3:ℝ) := by
  by_cases hn : n = 0
  · simp only [cubicThetaSeriesTerm,hn,ite_true,norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC
      (cubicWhittakerPowerConstant_pos (by omega : 1 ≤ 3)).le) (by positivity))
      (by positivity)) (Real.rpow_nonneg (norm_nonneg _) _)
  · simp only [cubicThetaSeriesTerm,hn,ite_false,norm_mul,Circle.norm_coe,mul_one]
    have hN := norm_pos_of_ne_zero hn
    calc
      _ ≤ (C*norm n)*((cubicWhittakerPowerConstant 3*81^(7/3:ℝ))*v^(-14/3:ℝ)*norm n^(-7/3:ℝ)) :=
        mul_le_mul (ha n hn) (cubicThetaWhittaker_frequency_bound hn hv)
          (_root_.norm_nonneg _) (mul_nonneg hC hN.le)
      _ = _ := by
        have he : norm n*norm n^(-7/3:ℝ) = norm n^(-4/3:ℝ) := by
          calc
            _ = norm n^(1:ℝ)*norm n^(-7/3:ℝ) := by rw [Real.rpow_one]
            _ = norm n^(1+(-7/3:ℝ)) := (Real.rpow_add hN _ _).symm
            _ = _ := by congr 1; ring
        calc
          _ = (C*cubicWhittakerPowerConstant 3*81^(7/3:ℝ)*v^(-14/3:ℝ))*
            (norm n*norm n^(-7/3:ℝ)) := by ring
          _ = _ := by rw [he]

/-- Absolute convergence needs only this coarse coefficient bound; the
arithmetic theta coefficient formulas are constructed separately. -/
theorem cubicThetaSeries_summable {a : Eisenstein → ℂ} {C v : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, n ≠ 0 → ‖a n‖ ≤ C*norm n)
    (hv : 0 < v) (z : ℂ) : Summable (cubicThetaSeriesTerm a z v) := by
  apply ((summable_eisenstein_norm_rpow (by norm_num : (1:ℝ) < 4/3)).mul_left
    (C*cubicWhittakerPowerConstant 3*81^(7/3:ℝ)*v^(-14/3:ℝ))).of_norm_bounded
  intro n
  simpa only [neg_div] using cubicThetaSeriesTerm_bound hC ha hv z n

end CubicFirstMoment

end

end OAI
