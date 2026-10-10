import Mathlib
import OAI.Probability.SKBarriers.Gaussian.SmoothObservables

namespace OAI

section

section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter

namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem fiberGaussian_directional_stein (n : ℕ) (f : ParameterSpace n → ℝ)
    (hf : ContDiff ℝ 1 f) (hg : HasExpGrowth f) (hg' : HasExpGrowth (fderiv ℝ f))
    (x : ℝ) (a : Fin n → ℝ) :
    (∫ z, coordinateLinear n a z*f z ∂fiberGaussian n x) =
      ∫ z, fderiv ℝ f z (coordinateVector n a) ∂fiberGaussian n x := by
  have hi₁ (i : Fin n) : Integrable (fun z => coordinateProjection n i z*f z) (fiberGaussian n x) :=
    ((HasExpGrowth.linear _).mul hg).integrable_fiberGaussian n
      ((coordinateProjection n i).continuous.mul hf.continuous) x
  have hi₂ (i : Fin n) : Integrable (fun z => fderiv ℝ f z (coordinateAxis n i)) (fiberGaussian n x) :=
    (hg'.derivative_eval _).integrable_fiberGaussian n
      ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const) x
  simp only [coordinateLinear_apply,coordinateVector,map_sum,map_smul,smul_eq_mul,
    Finset.sum_mul,mul_assoc]
  rw [integral_finsetSum _ (fun i _ => (hi₁ i).const_mul (a i)),
    integral_finsetSum _ (fun i _ => (hi₂ i).const_mul (a i))]
  apply Finset.sum_congr rfl
  intro i _
  simp only [integral_const_mul]
  rw [fiberGaussian_stein n f hf hg hg' x i]

theorem coordinateLinear_coordinateVector (n : ℕ) (a : Fin n → ℝ) :
    coordinateLinear n a (coordinateVector n a) = ∑ i, (a i)^2 := by
  simp only [coordinateLinear_apply,coordinateVector,map_sum,map_smul,smul_eq_mul,
    coordinateProjection_coordinateAxis,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true,pow_two]

theorem fiberGaussian_quadratic_stein (n : ℕ) (f : ParameterSpace n → ℝ)
    (hf : ContDiff ℝ 2 f) (hg : HasExpGrowth f) (hg' : HasExpGrowth (fderiv ℝ f))
    (hg'' : HasExpGrowth (fderiv ℝ (fderiv ℝ f))) (x : ℝ) (a : Fin n → ℝ) :
    (∫ z, (coordinateLinear n a z)^2*f z ∂fiberGaussian n x) =
      (∑ i, (a i)^2)*(∫ z, f z ∂fiberGaussian n x) +
        ∫ z, fderiv ℝ (fderiv ℝ f) z (coordinateVector n a) (coordinateVector n a)
          ∂fiberGaussian n x := by
  let L := coordinateLinear n a
  let u := coordinateVector n a
  let g := fun z => L z*f z
  have hf₁ := hf.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hgc : ContDiff ℝ 1 g := L.contDiff.mul hf₁
  have hgg : HasExpGrowth g := (HasExpGrowth.linear L).mul hg
  have hdg (z) : fderiv ℝ g z = L z • fderiv ℝ f z+f z • L := by
    simpa only [g,L.fderiv,Pi.mul_def] using fderiv_mul (L.differentiable z) (hf₁.differentiable (by norm_num) z)
  have hgg' : HasExpGrowth (fderiv ℝ g) := by
    rw [funext hdg]
    exact ((HasExpGrowth.linear L).smul hg').add (hg.smul (HasExpGrowth.const L))
  have H₁ := fiberGaussian_directional_stein n g hgc hgg hgg' x a
  have hwc := directionalGradient_contDiff f hf u
  have hwg : HasExpGrowth (directionalGradient f u) := hg'.derivative_eval u
  have hwg' : HasExpGrowth (fderiv ℝ (directionalGradient f u)) := by
    apply hg''.congr_bound (norm_nonneg u)
    intro z
    rw [fderiv_directionalGradient f hf]
    calc
      ‖(fderiv ℝ (fderiv ℝ f) z).flip u‖ ≤
          ‖(fderiv ℝ (fderiv ℝ f) z).flip‖*‖u‖ :=
        (fderiv ℝ (fderiv ℝ f) z).flip.le_opNorm u
      _ = ‖u‖*‖fderiv ℝ (fderiv ℝ f) z‖ := by
        rw [ContinuousLinearMap.opNorm_flip]
        ring
  have H₂ := fiberGaussian_directional_stein n (directionalGradient f u) hwc hwg hwg' x a
  have hi₁ : Integrable f (fiberGaussian n x) := hg.integrable_fiberGaussian n hf.continuous x
  have hi₂ : Integrable (fun z => L z*directionalGradient f u z) (fiberGaussian n x) :=
    ((HasExpGrowth.linear L).mul hwg).integrable_fiberGaussian n (L.continuous.mul hwc.continuous) x
  have he (z) : fderiv ℝ g z u = (∑ i, (a i)^2)*f z+L z*directionalGradient f u z := by
    rw [hdg]
    simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul,
      L,u,coordinateLinear_coordinateVector,directionalGradient]
    ring
  change (∫ z, L z*g z ∂fiberGaussian n x) = ∫ z, fderiv ℝ g z u ∂fiberGaussian n x at H₁
  simp_rw [he] at H₁
  rw [integral_add (hi₁.const_mul _) hi₂,integral_const_mul,H₂] at H₁
  simpa only [g,L,u,pow_two,mul_assoc,fderiv_directionalGradient f hf,
    ContinuousLinearMap.flip_apply] using H₁

end SK.Analytic

end
end

end

end OAI
