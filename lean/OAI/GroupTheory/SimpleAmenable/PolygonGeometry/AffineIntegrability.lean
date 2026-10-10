import Mathlib
import OAI.GroupTheory.SimpleAmenable.RandomFields.AffineDensityDerivative

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section AffineIntegrability
open Classical MeasureTheory Matrix

theorem integrable_matrix_affine {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (a : ι → ℝ) (hA : IsUnit A.det)
    {f : (ι → ℝ) → ℝ} (hf : Integrable f) :
    Integrable (fun x => f (a+A*ᵥx)) := by
  have hm : Integrable f (Measure.map (matrixAffineEquiv A a hA) volume) := by
    rw [show (matrixAffineEquiv A a hA : (ι → ℝ) → (ι → ℝ))=
      (fun x => a+A*ᵥx) from funext (fun x => matrixAffineEquiv_apply A a x hA),
      map_matrix_affine_volume A a hA]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  convert! (integrable_map_equiv (matrixAffineEquiv A a hA) f).mp hm using 1

theorem integrable_matrix_affine_inverse {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (a : ι → ℝ) (hA : IsUnit A.det)
    {f : (ι → ℝ) → ℝ} (hf : Integrable f) :
    Integrable (fun y => f (A⁻¹*ᵥ(y-a))) := by
  have h := integrable_matrix_affine A⁻¹ (-(A⁻¹*ᵥa))
    (isUnit_iff_ne_zero.mpr (by
      rw [Matrix.det_nonsing_inv,Ring.inverse_eq_inv]
      exact inv_ne_zero hA.ne_zero)) hf
  convert! h using 1
  ext y
  rw [Matrix.mulVec_sub]
  simp only [sub_eq_add_neg,add_comm]

theorem affineNoiseRoot_integrable_square {ι : Type*} [Fintype ι]
    {f : ℝ → ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
    (A : Matrix ι ι ℝ) (a : ι → ℝ) (hA : IsUnit A.det) :
    Integrable (fun y : ι → ℝ => affineNoiseRoot f A a y^2) := by
  have ht : Integrable (fun x : ι → ℝ => noiseTensor (fun _ : ι => f) x^2) := by
    convert! noiseTensor_integrable_inner (fun _ : ι => f)
      (fun _ : ι => f) (fun _ => ((hf.mul hf).integrable_of_hasCompactSupport
        (hc.mul_right (f' := f)))) using 1
    ext x
    simp only [pow_two]
  simpa only [affineNoiseRoot,div_pow] using
    (integrable_matrix_affine_inverse A a hA ht).div_const ((Real.sqrt A.det)^2)

theorem integrable_square_add {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {f g : X → ℝ} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ)
    (hf2 : Integrable (fun x => f x^2) μ) (hg2 : Integrable (fun x => g x^2) μ) :
    Integrable (fun x => (f x+g x)^2) μ := by
  apply ((hf2.add hg2).const_mul 2).mono' ((hf.add hg).pow 2)
  filter_upwards with x
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  simp only [Pi.add_apply,Pi.pow_apply]
  nlinarith [sq_nonneg (f x-g x)]

end AffineIntegrability

end SimpleAmenable
end
end

end OAI
