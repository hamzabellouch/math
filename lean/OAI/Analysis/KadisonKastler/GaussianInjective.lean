import OAI.Analysis.KadisonKastler.GaussianSeparation
import OAI.Analysis.KadisonKastler.GaussianStateCovariance

namespace OAI

/-! # Injectivity of Gaussian smearing for a strongly continuous unitary action -/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

theorem gaussianStateAverage_eq_zero (a : H →L[ℂ] H) (r : ℝ) (hr : 0 < r)
    (hzero : gaussianStateAverage U hU a r hr 0 = 0) : a = 0 := by
  have hz (s : ℝ) : gaussianStateAverage U hU a r hr s = 0 := by
    have he := gaussianStateAverage_covariance U hU a r hr 0 s
    rw [hzero] at he
    simpa [unitaryConj] using he.symm
  apply ContinuousLinearMap.ext
  intro x
  let y := a x
  let g : ℝ → ℂ := fun t => inner ℂ y (stateActionOrbit U a t x)
  have hg : Continuous g := continuous_const.inner (stateActionOrbit_continuous U hU a x)
  have hb (t : ℝ) : ‖g t‖ ≤ ‖y‖ * (‖a‖ * ‖x‖) := by
    apply (norm_inner_le_norm _ _).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg y)
    exact ((stateActionOrbit U a t).le_opNorm x).trans_eq (by rw [stateActionOrbit_norm])
  have hgi (s : ℝ) : (∫ t : ℝ, gaussianStateKernel r s t * g t) = 0 := by
    have hi := integrable_weighted_operator_vector volume (gaussianStateKernel r s)
      (gaussianStateKernel_integrable hr s) (stateActionOrbit U a)
      (fun x => (stateActionOrbit_continuous U hU a x).aestronglyMeasurable)
      ‖a‖ (Eventually.of_forall fun t => (stateActionOrbit_norm U a t).le) x
    calc
      _ = ∫ t : ℝ, (innerSL ℂ y) (gaussianStateKernel r s t • stateActionOrbit U a t x) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun t => (inner_smul_right _ _ _).symm
      _ = (innerSL ℂ y) (gaussianStateAverage U hU a r hr s x) :=
        (innerSL ℂ y).integral_comp_comm hi
      _ = 0 := by rw [hz]; simp
  have he := congrFun (zero_of_gaussian_averages r hr g hg _ hb hgi) 0
  have hv : inner ℂ (a x) (a x) = 0 := by
    simpa [g, y, stateActionOrbit, unitaryConj] using he
  exact inner_self_eq_zero.mp hv

theorem gaussianStateAverage_sub (a b : H →L[ℂ] H) (r : ℝ) (hr : 0 < r) (z : ℂ) :
    gaussianStateAverage U hU (a - b) r hr z =
      gaussianStateAverage U hU a r hr z - gaussianStateAverage U hU b r hr z := by
  apply ContinuousLinearMap.ext
  intro x
  have hi (c : H →L[ℂ] H) := integrable_weighted_operator_vector volume (gaussianStateKernel r z)
    (gaussianStateKernel_integrable hr z) (stateActionOrbit U c)
    (fun y => (stateActionOrbit_continuous U hU c y).aestronglyMeasurable)
    ‖c‖ (Eventually.of_forall fun t => (stateActionOrbit_norm U c t).le) x
  change (∫ t, gaussianStateKernel r z t • stateActionOrbit U (a - b) t x) =
    (∫ t, gaussianStateKernel r z t • stateActionOrbit U a t x) -
      (∫ t, gaussianStateKernel r z t • stateActionOrbit U b t x)
  rw [← integral_sub (hi a) (hi b)]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [stateActionOrbit, unitaryConj, mul_sub, sub_mul,
    sub_apply, smul_sub]

theorem gaussianStateAverage_injective (r : ℝ) (hr : 0 < r) :
    Function.Injective (fun a => gaussianStateAverage U hU a r hr 0) := by
  intro a b hab
  change gaussianStateAverage U hU a r hr 0 = gaussianStateAverage U hU b r hr 0 at hab
  apply sub_eq_zero.mp
  apply gaussianStateAverage_eq_zero U hU (a - b) r hr
  rw [gaussianStateAverage_sub, hab, sub_self]

end

end KadisonKastler

end OAI
