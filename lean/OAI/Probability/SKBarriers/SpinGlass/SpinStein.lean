import Mathlib
import OAI.Probability.SKBarriers.Gaussian.FiberGaussianStein

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
section SpinStein
variable {S : Type} [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]

def spinGaussianLaw (n : ℕ) (V : S → ParameterSpace n → ℝ) (x : ℝ) :
    Measure (S × ParameterSpace n) :=
  ((Measure.count : Measure S).prod (fiberGaussian n x)).tilted (fun sz => V sz.1 sz.2)

omit [Nonempty S] in
theorem finite_fiberGaussian_integrable (n : ℕ) (g : S → ParameterSpace n → ℝ)
    (hc : ∀ s, Continuous (g s)) (hi : ∀ s, Integrable (g s) (fiberGaussian n 0)) :
    Integrable (fun sz : S × ParameterSpace n => g sz.1 sz.2)
      ((Measure.count : Measure S).prod (fiberGaussian n 0)) := by
  apply (integrable_prod_iff ?_).2
  · exact ⟨ae_of_all _ hi,Integrable.of_finite⟩
  · exact (measurable_from_prod_countable_right (fun s => (hc s).measurable)).aestronglyMeasurable

theorem spinGaussianLaw_probability (n : ℕ) (V : S → ParameterSpace n → ℝ)
    (hV : ∀ s, BoundedDerivs (V s)) : IsProbabilityMeasure (spinGaussianLaw n V 0) := by
  let : NeZero ((Measure.count : Measure S).prod (fiberGaussian n 0)) := by
    refine ⟨Measure.measure_univ_ne_zero.mp ?_⟩
    rw [← univ_prod_univ,Measure.prod_prod]
    exact mul_ne_zero (NeZero.ne _) (NeZero.ne _)
  apply isProbabilityMeasure_tilted
  apply finite_fiberGaussian_integrable n _ (fun s => (Real.continuous_exp.comp (hV s).1.continuous))
  intro s
  have hg := ((hV s).exp_growths 1).1
  simp only [one_mul] at hg
  exact hg.integrable_fiberGaussian n (Real.continuous_exp.comp (hV s).1.continuous) 0

omit [Nonempty S] in

theorem spinGaussian_stein (n : ℕ) (V : S → ParameterSpace n → ℝ)
    (hV : ∀ s, BoundedDerivs (V s)) (B : S → ℝ) (i : Fin n) :
    (∫ sz, B sz.1*coordinateProjection n i sz.2 ∂spinGaussianLaw n V 0) =
      ∫ sz, B sz.1*fderiv ℝ (V sz.1) sz.2 (coordinateAxis n i) ∂spinGaussianLaw n V 0 := by
  have hg (s : S) : HasExpGrowth (fun z => Real.exp (V s z)) := by
    simpa only [one_mul] using ((hV s).exp_growths 1).1
  have hdg (s : S) : HasExpGrowth (fderiv ℝ (fun z => Real.exp (V s z))) := by
    simpa only [one_mul] using ((hV s).exp_growths 1).2.1
  have hd (s : S) : HasExpGrowth (fun z => fderiv ℝ (V s) z (coordinateAxis n i)) := by
    obtain ⟨_,C,D,hC,hD,hb,hbb⟩ := hV s
    exact (HasExpGrowth.of_bounded hC hb).derivative_eval _
  have ic (s : S) : Integrable (fun z => coordinateProjection n i z*Real.exp (V s z))
      (fiberGaussian n 0) :=
    ((HasExpGrowth.linear _).mul (hg s)).integrable_fiberGaussian n
      ((coordinateProjection n i).continuous.mul (Real.continuous_exp.comp (hV s).1.continuous)) 0
  have id (s : S) : Integrable
      (fun z => fderiv ℝ (V s) z (coordinateAxis n i)*Real.exp (V s z)) (fiberGaussian n 0) :=
    ((hd s).mul (hg s)).integrable_fiberGaussian n
      (((hV s).1.continuous_fderiv (by norm_num)).clm_apply continuous_const |>.mul
        (Real.continuous_exp.comp (hV s).1.continuous)) 0
  have il : Integrable
      (fun sz : S × ParameterSpace n => B sz.1*coordinateProjection n i sz.2*Real.exp (V sz.1 sz.2))
      ((Measure.count : Measure S).prod (fiberGaussian n 0)) := by
    simp_rw [mul_assoc]
    exact finite_fiberGaussian_integrable n _
      (fun s => continuous_const.mul ((coordinateProjection n i).continuous.mul
        (Real.continuous_exp.comp (hV s).1.continuous))) (fun s => (ic s).const_mul _)
  have ir : Integrable
      (fun sz : S × ParameterSpace n => B sz.1*
        fderiv ℝ (V sz.1) sz.2 (coordinateAxis n i)*Real.exp (V sz.1 sz.2))
      ((Measure.count : Measure S).prod (fiberGaussian n 0)) := by
    simp_rw [mul_assoc]
    exact finite_fiberGaussian_integrable n _
      (fun s => continuous_const.mul
        (((hV s).1.continuous_fderiv (by norm_num)).clm_apply continuous_const |>.mul
          (Real.continuous_exp.comp (hV s).1.continuous))) (fun s => (id s).const_mul _)
  simp only [spinGaussianLaw,integral_tilted_real_eq_div]
  congr 1
  rw [integral_prod _ il,integral_prod _ ir,integral_count,integral_count]
  apply Finset.sum_congr rfl
  intro s _
  simp only [mul_assoc,integral_const_mul]
  congr 1
  have H := fiberGaussian_stein n (fun z => Real.exp (V s z))
    ((hV s).1.exp.of_le (by norm_num)) (hg s) (hdg s) 0 i
  rw [H]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [((hV s).1.differentiable (by norm_num) z).hasFDerivAt.exp.fderiv]
  simp only [smul_apply,smul_eq_mul,mul_comm]

end SpinStein
end SK.Analytic

end
end
end
end
end
end
end

end OAI
