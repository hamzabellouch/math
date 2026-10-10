import Mathlib
import OAI.Probability.SKBarriers.Gaussian.GaussianQuadraticIBP

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem fiberGaussian_tilted_directional_stein_tent (n : ℕ) (V g : ParameterSpace n → ℝ)
    (hV : BoundedDerivs V) (hc : ContDiff ℝ 1 g)
    (hg : HasExpGrowth g) (hdg : HasExpGrowth (fderiv ℝ g)) (x : ℝ) (a : Fin n → ℝ) :
    (∫ z, coordinateLinear n a z*g z ∂(fiberGaussian n x).tilted V) =
      (∫ z, fderiv ℝ g z (coordinateVector n a) ∂(fiberGaussian n x).tilted V) +
      ∫ z, g z*fderiv ℝ V z (coordinateVector n a) ∂(fiberGaussian n x).tilted V := by
  have hdV : HasExpGrowth (fderiv ℝ V) := by
    obtain ⟨_,C,D,hC,hD,hb,hbb⟩ := hV
    exact HasExpGrowth.of_bounded hC hb
  have hi₁ (i : Fin n) := ((HasExpGrowth.linear (coordinateProjection n i)).mul hg).integrable_tilted_fiberGaussian
    n V hV ((coordinateProjection n i).continuous.mul hc.continuous) x
  have hi₂ (i : Fin n) := (hdg.derivative_eval (coordinateAxis n i)).integrable_tilted_fiberGaussian
    n V hV ((hc.continuous_fderiv (by norm_num)).clm_apply continuous_const) x
  have hi₃ (i : Fin n) := (hg.mul (hdV.derivative_eval (coordinateAxis n i))).integrable_tilted_fiberGaussian
    n V hV (hc.continuous.mul ((hV.1.continuous_fderiv (by norm_num)).clm_apply continuous_const)) x
  simp only [coordinateLinear_apply,coordinateVector,map_sum,map_smul,smul_eq_mul,
    Finset.sum_mul,Finset.mul_sum,mul_assoc]
  rw [integral_finsetSum _ (fun i _ => (hi₁ i).const_mul (a i)),
    integral_finsetSum _ (fun i _ => (hi₂ i).const_mul (a i))]
  have he : (fun z : ParameterSpace n => ∑ i, g z*(a i*fderiv ℝ V z (coordinateAxis n i)))=
      fun z => ∑ i, a i*(g z*fderiv ℝ V z (coordinateAxis n i)) := by
    funext z; apply Finset.sum_congr rfl; intro i _; ring
  rw [he,integral_finsetSum _ (fun i _ => (hi₃ i).const_mul (a i)),← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [integral_const_mul]
  rw [fiberGaussian_tilted_weighted_stein n V g hV hc hg hdg,mul_add]

theorem fiberGaussian_tilted_quadratic_invariant (n : ℕ) (V g : ParameterSpace n → ℝ)
    (hV : BoundedDerivs V) (hc : ContDiff ℝ 1 g)
    (hg : HasExpGrowth g) (hdg : HasExpGrowth (fderiv ℝ g)) (x : ℝ)
    (a : Fin n → ℝ) (hinv : TranslationInvariant g (coordinateVector n a)) :
    (∫ z, (coordinateLinear n a z)^2*g z ∂(fiberGaussian n x).tilted V) =
      (∑ i, (a i)^2)*(∫ z, g z ∂(fiberGaussian n x).tilted V) +
      ∫ z, g z*((fderiv ℝ (V ) z (coordinateVector n a))^2+
        fderiv ℝ (fderiv ℝ (V )) z (coordinateVector n a) (coordinateVector n a))
          ∂(fiberGaussian n x).tilted V := by
  let L := coordinateLinear n a
  let u := coordinateVector n a
  let d := directionalGradient V u
  have hdc : ContDiff ℝ 1 d := directionalGradient_contDiff V hV.1 u
  have hdg₀ := (hV.directionalGradient_bounds u).1
  have hdg₁ := (hV.directionalGradient_bounds u).2
  have hz (z) : fderiv ℝ g z u = 0 :=
    hinv.fderiv_zero (hc.differentiable (by norm_num)) z
  have hLc : ContDiff ℝ 1 (fun z => L z*g z) := L.contDiff.mul hc
  have hLg : HasExpGrowth (fun z => L z*g z) := (HasExpGrowth.linear L).mul hg
  have hLdg : HasExpGrowth (fderiv ℝ (fun z => L z*g z)) :=
    HasExpGrowth.fderiv_mul L.differentiable (hc.differentiable (by norm_num))
      (HasExpGrowth.linear L) hg (by
        apply HasExpGrowth.of_bounded (norm_nonneg L)
        intro z
        rw [L.fderiv]) hdg
  have H₁ := fiberGaussian_tilted_directional_stein_tent n V (fun z => L z*g z)
    hV hLc hLg hLdg x a
  have he₁ (z) : fderiv ℝ (fun z => L z*g z) z (coordinateVector n a) = (∑ i, (a i)^2)*g z := by
    change fderiv ℝ (fun z => L z*g z) z u = _
    rw [fderiv_fun_mul (L.differentiable z) (hc.differentiable (by norm_num) z)]
    simp only [add_apply,smul_apply,smul_eq_mul,hz,L.fderiv,zero_mul,zero_add,
      L,u,coordinateLinear_coordinateVector,mul_comm]
  simp_rw [he₁] at H₁
  rw [integral_const_mul] at H₁
  have hgc : ContDiff ℝ 1 (fun z => g z*d z) := hc.mul hdc
  have hgg : HasExpGrowth (fun z => g z*d z) := hg.mul hdg₀
  have hgg' : HasExpGrowth (fderiv ℝ (fun z => g z*d z)) :=
    HasExpGrowth.fderiv_mul (hc.differentiable (by norm_num))
      (hdc.differentiable (by norm_num)) hg hdg₀ hdg hdg₁
  have H₂ := fiberGaussian_tilted_directional_stein_tent n V (fun z => g z*d z)
    hV hgc hgg hgg' x a
  have he₂ (z) : fderiv ℝ (fun z => g z*d z) z (coordinateVector n a) =
      g z*fderiv ℝ d z u := by
    change fderiv ℝ (fun z => g z*d z) z u = _
    rw [fderiv_fun_mul (hc.differentiable (by norm_num) z)
      (hdc.differentiable (by norm_num) z)]
    simp only [add_apply,smul_apply,smul_eq_mul,hz,mul_zero,add_zero]
  simp_rw [he₂] at H₂
  have hi₁ := (hg.mul (hdg₁.derivative_eval u)).integrable_tilted_fiberGaussian n V hV
    (hc.continuous.mul ((hdc.continuous_fderiv (by norm_num)).clm_apply continuous_const)) x
  have hi₂ := ((hg.mul hdg₀).mul hdg₀).integrable_tilted_fiberGaussian n V hV
    ((hc.continuous.mul hdc.continuous).mul hdc.continuous) x
  change (∫ z, L z*(g z*d  z) ∂(fiberGaussian n x).tilted V) =
    (∫ z, g z*fderiv ℝ (d ) z u ∂(fiberGaussian n x).tilted V)+
    ∫ z, g z*d  z*d  z ∂(fiberGaussian n x).tilted V at H₂
  rw [← integral_add hi₁ hi₂] at H₂
  have he₃ : (fun z : ParameterSpace n => L z*g z*
      fderiv ℝ (V ) z u) = fun z => L z*(g z*d  z) := by
    funext sz; simp only [d,directionalGradient,mul_assoc]
  change (∫ z, L z*(L z*g z) ∂(fiberGaussian n x).tilted V) =
    (∑ i, (a i)^2)*(∫ z, g z ∂(fiberGaussian n x).tilted V)+
    ∫ z, L z*g z*fderiv ℝ (V ) z u ∂(fiberGaussian n x).tilted V at H₁
  rw [he₃,H₂] at H₁
  convert H₁ using 1
  · apply integral_congr_ae; filter_upwards [] with z; dsimp only [L]; ring
  · congr 1
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [fderiv_directionalGradient _ hV.1,ContinuousLinearMap.flip_apply,
      directionalGradient,u]
    ring

end SK.Analytic

end
end

end OAI
