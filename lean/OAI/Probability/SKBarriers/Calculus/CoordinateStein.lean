import Mathlib
import OAI.Probability.SKBarriers.SpinGlass.SpinWeightedStein

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
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def coordinateVector (n : ℕ) (a : Fin n → ℝ) : ParameterSpace n :=
  ∑ i, a i • coordinateAxis n i

section DirectionalSpinStein
variable {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

theorem spinGaussian_directional_stein (n : ℕ) (V g : S → ParameterSpace n → ℝ)
    (hV : ∀ s, BoundedDerivs (V s)) (hc : ∀ s, ContDiff ℝ 1 (g s))
    (hg : ∀ s, HasExpGrowth (g s)) (hdg : ∀ s, HasExpGrowth (fderiv ℝ (g s))) (a : Fin n → ℝ) :
    (∫ sz, coordinateLinear n a sz.2*g sz.1 sz.2 ∂spinGaussianLaw n V 0) =
      (∫ sz, fderiv ℝ (g sz.1) sz.2 (coordinateVector n a) ∂spinGaussianLaw n V 0) +
      ∫ sz, g sz.1 sz.2*fderiv ℝ (V sz.1) sz.2 (coordinateVector n a) ∂spinGaussianLaw n V 0 := by
  have hdV (s : S) : HasExpGrowth (fderiv ℝ (V s)) := by
    obtain ⟨_,C,D,hC,hD,hb,hbb⟩ := hV s
    exact HasExpGrowth.of_bounded hC hb
  have hi₁ (i : Fin n) := spinGaussian_integrable n V
    (fun s z => coordinateProjection n i z*g s z) hV
    (fun s => (HasExpGrowth.linear _).mul (hg s))
    (fun s => (coordinateProjection n i).continuous.mul (hc s).continuous)
  have hi₂ (i : Fin n) := spinGaussian_integrable n V
    (fun s z => fderiv ℝ (g s) z (coordinateAxis n i)) hV
    (fun s => (hdg s).derivative_eval _)
    (fun s => ((hc s).continuous_fderiv (by norm_num)).clm_apply continuous_const)
  have hi₃ (i : Fin n) := spinGaussian_integrable n V
    (fun s z => g s z*fderiv ℝ (V s) z (coordinateAxis n i)) hV
    (fun s => (hg s).mul ((hdV s).derivative_eval _))
    (fun s => (hc s).continuous.mul (((hV s).1.continuous_fderiv (by norm_num)).clm_apply continuous_const))
  simp only [coordinateLinear_apply,coordinateVector,map_sum,map_smul,smul_eq_mul,
    Finset.sum_mul,Finset.mul_sum,mul_assoc]
  rw [integral_finsetSum _ (fun i _ => (hi₁ i).const_mul (a i)),
    integral_finsetSum _ (fun i _ => (hi₂ i).const_mul (a i))]
  have he : (fun sz : S × ParameterSpace n => ∑ i, g sz.1 sz.2*(a i*
      fderiv ℝ (V sz.1) sz.2 (coordinateAxis n i))) =
      fun sz => ∑ i, a i*(g sz.1 sz.2*fderiv ℝ (V sz.1) sz.2 (coordinateAxis n i)) := by
    funext sz
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he,integral_finsetSum _ (fun i _ => (hi₃ i).const_mul (a i)),← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [integral_const_mul]
  rw [spinGaussian_weighted_stein n V g hV hc hg hdg,mul_add]

end DirectionalSpinStein
end SK.Analytic

end
end
end
end
end
end
end

end OAI
