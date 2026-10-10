import Mathlib
import OAI.Probability.SKBarriers.SpinGlass.SpinStein
import OAI.Probability.SKBarriers.Scalar.GrowthOperations

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic
section SpinWeightedStein
variable {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

theorem spinGaussian_integrable (n : ℕ) (V g : S → ParameterSpace n → ℝ)
    (hV : ∀ s, BoundedDerivs (V s)) (hg : ∀ s, HasExpGrowth (g s))
    (hc : ∀ s, Continuous (g s)) :
    Integrable (fun sz : S × ParameterSpace n => g sz.1 sz.2) (spinGaussianLaw n V 0) := by
  have he (s : S) : HasExpGrowth (fun z => Real.exp (V s z)) := by
    simpa only [one_mul] using ((hV s).exp_growths 1).1
  have hce (s : S) := Real.continuous_exp.comp (hV s).1.continuous
  have hI := finite_fiberGaussian_integrable n _ hce
    (fun s => (he s).integrable_fiberGaussian n (hce s) 0)
  rw [spinGaussianLaw,integrable_tilted_iff hI]
  exact finite_fiberGaussian_integrable n _ (fun s => (hce s).smul (hc s))
    (fun s => ((he s).smul (hg s)).integrable_fiberGaussian n ((hce s).smul (hc s)) 0)

theorem spinGaussian_weighted_stein (n : ℕ) (V g : S → ParameterSpace n → ℝ)
    (hV : ∀ s, BoundedDerivs (V s)) (hc : ∀ s, ContDiff ℝ 1 (g s))
    (hg : ∀ s, HasExpGrowth (g s)) (hdg : ∀ s, HasExpGrowth (fderiv ℝ (g s))) (i : Fin n) :
    (∫ sz, coordinateProjection n i sz.2*g sz.1 sz.2 ∂spinGaussianLaw n V 0) =
      (∫ sz, fderiv ℝ (g sz.1) sz.2 (coordinateAxis n i) ∂spinGaussianLaw n V 0) +
      ∫ sz, g sz.1 sz.2*fderiv ℝ (V sz.1) sz.2 (coordinateAxis n i) ∂spinGaussianLaw n V 0 := by
  have he (s : S) : HasExpGrowth (fun z => Real.exp (V s z)) := by
    simpa only [one_mul] using ((hV s).exp_growths 1).1
  have hce (s : S) := Real.continuous_exp.comp (hV s).1.continuous
  have hdV (s : S) : HasExpGrowth (fderiv ℝ (V s)) := by
    obtain ⟨_,C,D,hC,hD,hb,hbb⟩ := hV s
    exact HasExpGrowth.of_bounded hC hb
  have hcdV (s : S) := (hV s).1.continuous_fderiv (by norm_num)
  have hcdg (s : S) := (hc s).continuous_fderiv (by norm_num)
  have il := finite_fiberGaussian_integrable n
    (fun s z => coordinateProjection n i z*g s z*Real.exp (V s z))
    (fun s => (((coordinateProjection n i).continuous.mul (hc s).continuous).mul (hce s)))
    (fun s => (((HasExpGrowth.linear _).mul (hg s)).mul (he s)).integrable_fiberGaussian n
      (((coordinateProjection n i).continuous.mul (hc s).continuous).mul (hce s)) 0)
  have ir₁ := finite_fiberGaussian_integrable n
    (fun s z => fderiv ℝ (g s) z (coordinateAxis n i)*Real.exp (V s z))
    (fun s => ((hcdg s).clm_apply continuous_const).mul (hce s))
    (fun s => (((hdg s).derivative_eval _).mul (he s)).integrable_fiberGaussian n
      (((hcdg s).clm_apply continuous_const).mul (hce s)) 0)
  have ir₂ := finite_fiberGaussian_integrable n
    (fun s z => g s z*fderiv ℝ (V s) z (coordinateAxis n i)*Real.exp (V s z))
    (fun s => ((hc s).continuous.mul ((hcdV s).clm_apply continuous_const)).mul (hce s))
    (fun s => (((hg s).mul ((hdV s).derivative_eval _)).mul (he s)).integrable_fiberGaussian n
      (((hc s).continuous.mul ((hcdV s).clm_apply continuous_const)).mul (hce s)) 0)
  simp only [spinGaussianLaw,integral_tilted_real_eq_div]
  rw [← add_div]
  congr 1
  rw [integral_prod _ il,integral_prod _ ir₁,integral_prod _ ir₂,
    integral_count,integral_count,integral_count,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  have H := fiberGaussian_tilted_weighted_stein n (V s) (g s) (hV s) (hc s) (hg s) (hdg s) 0 i
  simp only [integral_tilted_real_eq_div] at H
  rw [← add_div] at H
  exact (div_left_inj' (integral_exp_pos
    ((he s).integrable_fiberGaussian n (hce s) 0)).ne').mp H

end SpinWeightedStein
end SK.Analytic

end
end
end
end
end
end
end

end OAI
