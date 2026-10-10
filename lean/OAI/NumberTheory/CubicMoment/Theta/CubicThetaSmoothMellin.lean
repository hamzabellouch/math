import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAngularContour
import OAI.NumberTheory.CubicMoment.Estimates.MellinSeries

namespace OAI

/-! Mellin inversion for the literal arithmetic frequency coefficients.
The coefficient carries one frequency norm, so its Dirichlet variable is
`2*s-1`, exactly as in the theta Gamma completion. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaDirichlet_nonzero (a : Eisenstein→ℂ) (s : ℂ) :
    cubicThetaDirichlet a s = ∑' n : MetaplecticDualArgument,
      a n.val*(‖cubicThetaFrequency n.val‖:ℂ)^(-s) := by
  unfold cubicThetaDirichlet
  have hs : Function.support (fun n : Eisenstein =>
      if n=0 then (0:ℂ) else a n*(‖cubicThetaFrequency n‖:ℂ)^(-s)) ⊆ {n | n≠0} := by
    intro n hn hz
    exact hn (by simp [hz])
  rw [←tsum_subtype_eq_of_support_subset hs]
  apply tsum_congr
  intro n
  exact ite_eq_right n.property

lemma cubicTheta_norm_square_power {r : ℝ} (hr : 0<r) (s : ℂ) :
    (r:ℂ)*((r^2:ℝ):ℂ)^(-s) = (r:ℂ)^(-(2*s-1)) := by
  rw [Complex.ofReal_pow,←Complex.cpow_nat_mul'
    (by simpa [Complex.arg_ofReal_of_nonneg hr.le] using neg_neg_of_pos Real.pi_pos)
    (by simpa [Complex.arg_ofReal_of_nonneg hr.le] using Real.pi_pos.le)]
  calc
    _ = (r:ℂ)^((1:ℂ)+(2:ℂ)*(-s)) := by
      rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hr.ne'),Complex.cpow_one]
      norm_num
    _ = _ := by congr 1; ring

lemma cubicTheta_norm_square_weight {r : ℝ} (hr : 0<r) (σ : ℝ) :
    r*(r^2)^(-σ) = r^(-(2*σ-1)) := by
  rw [←Real.rpow_natCast r 2,←Real.rpow_mul hr.le]
  calc
    _ = r^(1+(2:ℝ)*(-σ)) := by rw [Real.rpow_add hr,Real.rpow_one]; norm_num
    _ = _ := by congr 1; ring

lemma cubicTheta_normDirichlet (a : Eisenstein→ℂ) (s : ℂ) :
    normDirichletSeries
      (fun n : MetaplecticDualArgument => a n.val*(‖cubicThetaFrequency n.val‖:ℂ))
      (fun n : MetaplecticDualArgument => ‖cubicThetaFrequency n.val‖^2) s =
        cubicThetaDirichlet a (2*s-1) := by
  rw [cubicThetaDirichlet_nonzero]
  unfold normDirichletSeries
  apply tsum_congr
  intro n
  rw [mul_assoc,cubicTheta_norm_square_power (cubicThetaFrequency_pos n.property)]

theorem cubicTheta_smooth_mellin {a : Eisenstein→ℂ} {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, ‖a n‖ ≤ C)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {σ Z : ℝ} (hσ : 3/2<σ) (hZ : 0<Z) :
    (∑' n : MetaplecticDualArgument,
      a n.val*(‖cubicThetaFrequency n.val‖:ℂ)*W (‖cubicThetaFrequency n.val‖^2/Z)) =
    ((1/(2*Real.pi):ℝ):ℂ)*∫ t : ℝ,
      mellin W (σ+(t:ℂ)*Complex.I)*(Z:ℂ)^(σ+(t:ℂ)*Complex.I)*
        cubicThetaDirichlet a (2*(σ+(t:ℂ)*Complex.I)-1) := by
  let : Countable Eisenstein := coordinatesEquiv.symm.injective.countable
  have habs := (cubicTheta_mellin_weight_summable hC ha
    (by linarith : 2<2*σ-1)).subtype (fun n : Eisenstein => n≠0)
  have hnorm : Summable (fun n : MetaplecticDualArgument =>
      ‖a n.val*(‖cubicThetaFrequency n.val‖:ℂ)‖*(‖cubicThetaFrequency n.val‖^2)^(-σ)) := by
    convert habs using 1
    funext n
    simp only [Function.comp_apply,n.property,ite_false,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (_root_.norm_nonneg _)]
    rw [mul_assoc,cubicTheta_norm_square_weight (cubicThetaFrequency_pos n.property)]
  have H := smooth_mellin_series
    (fun n : MetaplecticDualArgument => a n.val*(‖cubicThetaFrequency n.val‖:ℂ))
    (fun n : MetaplecticDualArgument => ‖cubicThetaFrequency n.val‖^2)
    (fun n => sq_pos_of_pos (cubicThetaFrequency_pos n.property)) W hW hpos hsm σ hnorm hZ
  simpa only [cubicTheta_normDirichlet] using H

lemma cubicThetaAdditive_angular_norm (ℓ : ℤ) (z : ℂ) (n : Eisenstein) :
    ‖theta ℓ n*cubicThetaAdditiveCoefficient z n‖ ≤ 81 := by
  by_cases hn : n=0
  · subst n
    have hz : cubicThetaArithmeticCoefficient 0=0 := by
      apply dite_eq_right
      rintro ⟨R⟩
      exact R.ne_zero rfl
    simp only [cubicThetaAdditiveCoefficient,hz,zero_mul,mul_zero,norm_zero]
    norm_num
  · rw [norm_mul,norm_theta hn,one_mul]
    exact cubicThetaAdditiveCoefficient_norm _ n

theorem cubicThetaAngular_smooth_continued {q : Eisenstein}
    (hq : primary q) (x y : Eisenstein) (hxy : q∣9*x*y-1) (rev : Bool)
    {k : ℕ} (hk : 0<k) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {σ Z : ℝ} (hσ : 3/2<σ) (hZ : 0<Z) :
    (∑' n : MetaplecticDualArgument,
      theta (cubicThetaCircleOrder rev k) n.val*
        cubicThetaAdditiveCoefficient (-(3*(x:ℂ)/(q:ℂ))) n.val*
        (‖cubicThetaFrequency n.val‖:ℂ)*W (‖cubicThetaFrequency n.val‖^2/Z)) =
    ((1/(2*Real.pi):ℝ):ℂ)*∫ t : ℝ,
      mellin W (σ+(t:ℂ)*Complex.I)*(Z:ℂ)^(σ+(t:ℂ)*Complex.I)*
        cubicThetaAngularDirichletContinuation q x y rev k (σ+(t:ℂ)*Complex.I) := by
  have ha (n : Eisenstein) : ‖theta (cubicThetaCircleOrder rev k) n*
      cubicThetaAdditiveCoefficient (-(3*(x:ℂ)/(q:ℂ))) n‖ ≤ 81 := by
    exact cubicThetaAdditive_angular_norm _ _ n
  rw [cubicTheta_smooth_mellin (by norm_num) ha W hW hpos hsm hσ hZ]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  rw [cubicThetaAngularDirichletContinuation_eq hq x y hxy rev hk (by simpa using hσ)]

end CubicFirstMoment

end

end OAI
