import OAI.NumberTheory.CubicMoment.Estimates.CubicWhittakerConvergence
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHeightDecay

namespace OAI

/-! Absolute lattice and kernel masses for exchanging the theta sum with
its Mellin integral on the initial right half-plane. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

def cubicWhittakerNormMass (σ : ℝ) : ℝ :=
  ∫ v in Ioi (0:ℝ), v^(σ-1)*‖cubicThetaWhittaker v‖

lemma cubicWhittakerNormMass_nonneg (σ : ℝ) : 0 ≤ cubicWhittakerNormMass σ := by
  apply setIntegral_nonneg measurableSet_Ioi
  intro v hv
  exact mul_nonneg (Real.rpow_nonneg hv.le _) (_root_.norm_nonneg _)

lemma cubicWhittaker_norm_integral_scale (u c : ℂ) {r : ℝ} (hr : 0 < r) :
    (∫ v in Ioi (0:ℝ), ‖(v:ℂ)^(u-1)*(c*cubicThetaWhittaker (r*v))‖) =
      ‖c‖*r^(-u.re)*cubicWhittakerNormMass u.re := by
  calc
    _ = ‖c‖*(∫ v in Ioi (0:ℝ), v^(u.re-1)*‖cubicThetaWhittaker (r*v)‖) := by
      rw [←integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      dsimp only
      rw [norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hv]
      simp only [Complex.sub_re,Complex.one_re]
      ring
    _ = _ := by rw [cubicWhittaker_norm_mass_scale u.re hr]; unfold cubicWhittakerNormMass; ring

/-- Bounded normalized coefficients give an absolutely convergent initial
Dirichlet series for Re u > 2. -/
lemma cubicTheta_mellin_weight_summable {a : Eisenstein → ℂ} {C σ : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, ‖a n‖ ≤ C) (hσ : 2 < σ) :
    Summable (fun n : Eisenstein => if n = 0 then (0:ℝ) else
      ‖a n‖*‖cubicThetaFrequency n‖^(-σ)) := by
  have hs : Summable (fun n : Eisenstein =>
      (C*81^(σ/2))*norm n^(-(σ/2))) :=
    (summable_eisenstein_norm_rpow (by linarith : 1 < σ/2)).mul_left _
  apply hs.of_nonneg_of_le
  · intro n
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (_root_.norm_nonneg _) (Real.rpow_nonneg (_root_.norm_nonneg _) _)
  · intro n
    by_cases hn : n = 0
    · rw [ite_eq_left hn]
      exact mul_nonneg (mul_nonneg hC (by positivity)) (Real.rpow_nonneg (norm_nonneg _) _)
    · rw [ite_eq_right hn,cubicThetaFrequency_rpow hn]
      have he1 : -(-σ)/2 = σ/2 := by ring
      have he2 : -σ/2 = -(σ/2) := by ring
      rw [he1,he2]
      calc
        _ ≤ C*(81^(σ/2)*norm n^(-(σ/2))) :=
          mul_le_mul_of_nonneg_right (ha n) (by positivity [norm_nonneg n])
        _ = _ := by ring

end CubicFirstMoment

end

end OAI
