import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFieldOperator
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralSubunitCoefficients

namespace OAI

/-! Operator-norm convergence of the bounded spectral field when the
nonlinear coefficient pair vanishes and the two exponents converge. -/

open Filter Topology
open scoped BoundedContinuousFunction
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

noncomputable def circularExponentDifference (νp νm μp μm : ℂ) : ℝ :=
  2*‖νp-μp‖+‖νp*(νp+10)-μp*(μp+10)‖+
  (2*‖νm-μm‖+‖νm*(νm+10)-μm*(μm+10)‖)

theorem circularExponentDifference_nonneg (νp νm μp μm : ℂ) :
    0 ≤ circularExponentDifference νp νm μp μm := by
  unfold circularExponentDifference
  positivity

theorem circularExponentDifference_tendsto (νp νm : ℕ → ℂ) (μp μm : ℂ)
    (hp : Tendsto νp atTop (𝓝 μp)) (hm : Tendsto νm atTop (𝓝 μm)) :
    Tendsto (fun n => circularExponentDifference (νp n) (νm n) μp μm) atTop (𝓝 0) := by
  have hp' := ((hp.mul (hp.add_const 10)).sub_const (μp*(μp+10))).norm
  have hm' := ((hm.mul (hm.add_const 10)).sub_const (μm*(μm+10))).norm
  simpa only [circularExponentDifference,sub_self,norm_zero,mul_zero,add_zero] using
    (((hp.sub_const μp).norm.const_mul 2).add hp').add
      (((hm.sub_const μm).norm.const_mul 2).add hm')

theorem circularBoundedField_exponent_bound (νp νm μp μm η : ℂ) (m : ℕ)
    (q : ℂ) (z : E₄) :
    ‖circularBoundedField νp νm η m q z-circularBoundedField μp μm η m q z‖ ≤
      circularExponentDifference νp νm μp μm*‖z‖ := by
  have he : circularBoundedField νp νm η m q z-circularBoundedField μp μm η m q z=
      ((0,-(2*(νp-μp))*z.1.2-(νp*(νp+10)-μp*(μp+10))*z.1.1),
       (0,-(2*(νm-μm))*z.2.2-(νm*(νm+10)-μm*(μm+10))*z.2.1)) := by
    apply Prod.ext <;> apply Prod.ext <;> simp only [circularBoundedField,Prod.fst_sub,Prod.snd_sub]
    all_goals ring
  have hrow (a b x y : ℂ) (hx : ‖x‖ ≤ ‖z‖) (hy : ‖y‖ ≤ ‖z‖) :
      ‖-(2*a)*x-b*y‖ ≤ (2*‖a‖+‖b‖)*‖z‖ := by
    calc
      _ ≤ ‖-(2*a)*x‖+‖b*y‖ := norm_sub_le _ _
      _ = (2*‖a‖)*‖x‖+‖b‖*‖y‖ := by simp only [norm_mul,norm_neg,Complex.norm_ofNat]
      _ ≤ (2*‖a‖)*‖z‖+‖b‖*‖z‖ := by gcongr
      _ = _ := by ring
  have hp := hrow (νp-μp) (νp*(νp+10)-μp*(μp+10)) z.1.2 z.1.1
    ((norm_snd_le _).trans (norm_fst_le z)) ((norm_fst_le _).trans (norm_fst_le z))
  have hm := hrow (νm-μm) (νm*(νm+10)-μm*(μm+10)) z.2.2 z.2.1
    ((norm_snd_le _).trans (norm_snd_le z)) ((norm_fst_le _).trans (norm_snd_le z))
  rw [he]
  change max (max ‖(0 : ℂ)‖ _) (max ‖(0 : ℂ)‖ _) ≤ _
  simp only [norm_zero,max_eq_right (norm_nonneg _)]
  apply max_le
  · exact hp.trans (mul_le_mul_of_nonneg_right (by unfold circularExponentDifference; exact le_add_of_nonneg_right (by positivity)) (norm_nonneg z))
  · exact hm.trans (mul_le_mul_of_nonneg_right (by unfold circularExponentDifference; exact le_add_of_nonneg_left (by positivity)) (norm_nonneg z))

theorem circularBoundedField_free_bound (νp νm μp μm η : ℂ) (m : ℕ) (hm : 1 ≤ m)
    (q : ℂ) (δ : ℝ)
    (hq : ‖spectralDiagonalCoefficient m q‖+‖spectralCrossCoefficient m q‖ ≤ δ) (z : E₄) :
    ‖circularBoundedField νp νm η m q z-circularBoundedField μp μm η 1 0 z‖ ≤
      (circularExponentDifference νp νm μp μm+δ)*‖z‖ := by
  have he : circularBoundedField μp μm η m 0 z=circularBoundedField μp μm η 1 0 z := by
    simp only [circularBoundedField,(spectralCoefficient_zero m hm).1,
      (spectralCoefficient_zero m hm).2,(spectralCoefficient_zero 1 (by omega)).1,
      (spectralCoefficient_zero 1 (by omega)).2]
  have hc : ‖circularBoundedField μp μm η m q z-circularBoundedField μp μm η m 0 z‖ ≤ δ*‖z‖ := by
    rw [circularBoundedField_coefficient_difference,(spectralCoefficient_zero m hm).1,
      (spectralCoefficient_zero m hm).2,sub_zero,sub_zero]
    exact (circularCoefficientAction_norm _ _ z).trans (mul_le_mul_of_nonneg_right hq (norm_nonneg z))
  calc
    _ ≤ ‖circularBoundedField νp νm η m q z-circularBoundedField μp μm η m q z‖+
        ‖circularBoundedField μp μm η m q z-circularBoundedField μp μm η 1 0 z‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ circularExponentDifference νp νm μp μm*‖z‖+δ*‖z‖ := by
      rw [← he]
      exact add_le_add (circularBoundedField_exponent_bound _ _ _ _ _ _ _ _) hc
    _ = _ := by ring

theorem circularFieldOperator_free_bound (νp νm μp μm η : ℂ) (m : ℕ) (hm : 1 ≤ m)
    (q : ℝ →ᵇ ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hq : ∀ t, ‖spectralDiagonalCoefficient m (q t)‖+‖spectralCrossCoefficient m (q t)‖ ≤ δ) :
    ‖circularFieldOperator νp νm η m hm q-circularFieldOperator μp μm η 1 (by omega) 0‖ ≤
      circularExponentDifference νp νm μp μm+δ := by
  let C := circularExponentDifference νp νm μp μm+δ
  have hC : 0 ≤ C := add_nonneg (circularExponentDifference_nonneg _ _ _ _) hδ
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro v
  have hb (t : ℝ) := (circularBoundedField_free_bound νp νm μp μm η m hm (q t) δ (hq t)
    (circularTailEvaluation v t)).trans
    (mul_le_mul_of_nonneg_left (circularTailEvaluation_norm v t) hC)
  change max ‖(circularFieldOperator νp νm η m hm q v-
      circularFieldOperator μp μm η 1 (by omega) 0 v).1‖
    ‖(circularFieldOperator νp νm η m hm q v-
      circularFieldOperator μp μm η 1 (by omega) 0 v).2‖ ≤ C*‖v‖
  apply max_le
  · apply (BoundedContinuousFunction.norm_le (mul_nonneg hC (norm_nonneg v))).2
    intro t
    exact (norm_fst_le _).trans (hb t)
  · apply (BoundedContinuousFunction.norm_le (mul_nonneg hC (norm_nonneg v))).2
    intro t
    exact (norm_snd_le _).trans (hb t)

noncomputable local instance circularOperatorNormed :
    NormedAddCommGroup (CircularTailSpace →L[ℂ] CircularTailSpace) := by
  letI : NormedAddCommGroup CircularTailSpace := inferInstance
  letI : NormedSpace ℂ CircularTailSpace := inferInstance
  exact ContinuousLinearMap.toNormedAddCommGroup

theorem circularFieldOperator_free_tendsto (νp νm : ℕ → ℂ) (μp μm η : ℂ)
    (hp : Tendsto νp atTop (𝓝 μp)) (hn : Tendsto νm atTop (𝓝 μm))
    (m : ℕ → ℕ) (hm : ∀ n, 1 ≤ m n) (q : ℕ → ℝ →ᵇ ℂ)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n) (hδ0 : Tendsto δ atTop (𝓝 0))
    (hq : ∀ᶠ n in atTop, ∀ t,
      ‖spectralDiagonalCoefficient (m n) (q n t)‖+‖spectralCrossCoefficient (m n) (q n t)‖ ≤ δ n) :
    Tendsto (fun n => circularFieldOperator (νp n) (νm n) η (m n) (hm n) (q n)) atTop
      (𝓝 (circularFieldOperator μp μm η 1 (by omega) 0)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hlim := (circularExponentDifference_tendsto νp νm μp μm hp hn).add hδ0
  simp only [add_zero] at hlim
  exact squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
    (hq.mono (fun n he => circularFieldOperator_free_bound _ _ _ _ _ _ _ _ _ (hδ n) he)) hlim

end DefocusingNLS

end OAI
