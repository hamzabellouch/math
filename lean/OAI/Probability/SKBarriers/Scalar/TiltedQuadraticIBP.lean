import Mathlib
import OAI.Probability.SKBarriers.Gaussian.GaussianQuadraticIBP

namespace OAI

section

section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter

namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

section TiltedQuadratic
variable {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

theorem spinGaussian_quadratic_invariant (n : ℕ) (V g : S → ParameterSpace n → ℝ)
    (hV : ∀ s, BoundedDerivs (V s)) (hc : ∀ s, ContDiff ℝ 1 (g s))
    (hg : ∀ s, HasExpGrowth (g s)) (hdg : ∀ s, HasExpGrowth (fderiv ℝ (g s)))
    (a : Fin n → ℝ) (hinv : ∀ s, TranslationInvariant (g s) (coordinateVector n a)) :
    (∫ sz, (coordinateLinear n a sz.2)^2*g sz.1 sz.2 ∂spinGaussianLaw n V 0) =
      (∑ i, (a i)^2)*(∫ sz, g sz.1 sz.2 ∂spinGaussianLaw n V 0) +
      ∫ sz, g sz.1 sz.2*((fderiv ℝ (V sz.1) sz.2 (coordinateVector n a))^2+
        fderiv ℝ (fderiv ℝ (V sz.1)) sz.2 (coordinateVector n a) (coordinateVector n a))
          ∂spinGaussianLaw n V 0 := by
  let L := coordinateLinear n a
  let u := coordinateVector n a
  let d := fun s => directionalGradient (V s) u
  have hdc (s) : ContDiff ℝ 1 (d s) := directionalGradient_contDiff (V s) (hV s).1 u
  have hdg₀ (s) := ((hV s).directionalGradient_bounds u).1
  have hdg₁ (s) := ((hV s).directionalGradient_bounds u).2
  have hz (s) (z) : fderiv ℝ (g s) z u = 0 :=
    (hinv s).fderiv_zero ((hc s).differentiable (by norm_num)) z
  have hLc (s) : ContDiff ℝ 1 (fun z => L z*g s z) := L.contDiff.mul (hc s)
  have hLg (s) : HasExpGrowth (fun z => L z*g s z) := (HasExpGrowth.linear L).mul (hg s)
  have hLdg (s) : HasExpGrowth (fderiv ℝ (fun z => L z*g s z)) :=
    HasExpGrowth.fderiv_mul L.differentiable ((hc s).differentiable (by norm_num))
      (HasExpGrowth.linear L) (hg s) (by
        apply HasExpGrowth.of_bounded (norm_nonneg L)
        intro z
        rw [L.fderiv]) (hdg s)
  have H₁ := spinGaussian_directional_stein n V (fun s z => L z*g s z)
    hV hLc hLg hLdg a
  have he₁ (s) (z) : fderiv ℝ (fun z => L z*g s z) z (coordinateVector n a) = (∑ i, (a i)^2)*g s z := by
    change fderiv ℝ (fun z => L z*g s z) z u = _
    rw [fderiv_fun_mul (L.differentiable z) ((hc s).differentiable (by norm_num) z)]
    simp only [add_apply,smul_apply,smul_eq_mul,hz,L.fderiv,zero_mul,zero_add,
      L,u,coordinateLinear_coordinateVector,mul_comm]
  simp_rw [he₁] at H₁
  rw [integral_const_mul] at H₁
  have hgc (s) : ContDiff ℝ 1 (fun z => g s z*d s z) := (hc s).mul (hdc s)
  have hgg (s) : HasExpGrowth (fun z => g s z*d s z) := (hg s).mul (hdg₀ s)
  have hgg' (s) : HasExpGrowth (fderiv ℝ (fun z => g s z*d s z)) :=
    HasExpGrowth.fderiv_mul ((hc s).differentiable (by norm_num))
      ((hdc s).differentiable (by norm_num)) (hg s) (hdg₀ s) (hdg s) (hdg₁ s)
  have H₂ := spinGaussian_directional_stein n V (fun s z => g s z*d s z)
    hV hgc hgg hgg' a
  have he₂ (s) (z) : fderiv ℝ (fun z => g s z*d s z) z (coordinateVector n a) =
      g s z*fderiv ℝ (d s) z u := by
    change fderiv ℝ (fun z => g s z*d s z) z u = _
    rw [fderiv_fun_mul ((hc s).differentiable (by norm_num) z)
      ((hdc s).differentiable (by norm_num) z)]
    simp only [add_apply,smul_apply,smul_eq_mul,hz,mul_zero,add_zero]
  simp_rw [he₂] at H₂
  have hi₁ := spinGaussian_integrable n V (fun s z => g s z*fderiv ℝ (d s) z u) hV
    (fun s => (hg s).mul ((hdg₁ s).derivative_eval u))
    (fun s => (hc s).continuous.mul (((hdc s).continuous_fderiv (by norm_num)).clm_apply continuous_const))
  have hi₂ := spinGaussian_integrable n V (fun s z => g s z*d s z*d s z) hV
    (fun s => ((hg s).mul (hdg₀ s)).mul (hdg₀ s))
    (fun s => ((hc s).continuous.mul (hdc s).continuous).mul (hdc s).continuous)
  change (∫ sz, L sz.2*(g sz.1 sz.2*d sz.1 sz.2) ∂spinGaussianLaw n V 0) =
    (∫ sz, g sz.1 sz.2*fderiv ℝ (d sz.1) sz.2 u ∂spinGaussianLaw n V 0)+
    ∫ sz, g sz.1 sz.2*d sz.1 sz.2*d sz.1 sz.2 ∂spinGaussianLaw n V 0 at H₂
  rw [← integral_add hi₁ hi₂] at H₂
  have he₃ : (fun sz : S × ParameterSpace n => L sz.2*g sz.1 sz.2*
      fderiv ℝ (V sz.1) sz.2 u) = fun sz => L sz.2*(g sz.1 sz.2*d sz.1 sz.2) := by
    funext sz; simp only [d,directionalGradient,mul_assoc]
  change (∫ sz, L sz.2*(L sz.2*g sz.1 sz.2) ∂spinGaussianLaw n V 0) =
    (∑ i, (a i)^2)*(∫ sz, g sz.1 sz.2 ∂spinGaussianLaw n V 0)+
    ∫ sz, L sz.2*g sz.1 sz.2*fderiv ℝ (V sz.1) sz.2 u ∂spinGaussianLaw n V 0 at H₁
  rw [he₃,H₂] at H₁
  convert H₁ using 1
  · apply integral_congr_ae; filter_upwards [] with sz; dsimp only [L]; ring
  · congr 1
    apply integral_congr_ae
    filter_upwards [] with sz
    simp only [d,fderiv_directionalGradient _ (hV _).1,ContinuousLinearMap.flip_apply,
      directionalGradient,u]
    ring

end TiltedQuadratic
end SK.Analytic

end
end

end

end OAI
