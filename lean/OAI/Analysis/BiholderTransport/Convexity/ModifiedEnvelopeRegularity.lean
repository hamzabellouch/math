import Mathlib
import OAI.Analysis.BiholderTransport.Contact.Subgradient
import OAI.Analysis.BiholderTransport.Calculus.SecondDerivativeTaylor
import OAI.Analysis.BiholderTransport.LinearAlgebra.EigenOrder

namespace OAI

noncomputable section

namespace WeakMTWTransport

section

open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma differentiableAt_of_const_mul {f : E → ℝ} {t : ℝ} (ht : t≠0) {x:E}
    (hd : DifferentiableAt ℝ (fun z => t*f z) x) :
    HasFDerivAt f (t⁻¹ • fderiv ℝ (fun z => t*f z) x) x := by
  have H := hd.hasFDerivAt.const_mul t⁻¹
  simpa only [←mul_assoc,inv_mul_cancel₀ ht,one_mul] using H

lemma C11_const_mul_cancel {f : E → ℝ} {S : Set E} {t : ℝ} {K : ℝ≥0}
    (ht : t≠0) (hd : ∀ x∈S,DifferentiableAt ℝ (fun z => t*f z) x)
    (hLip : LipschitzOnWith K (fderiv ℝ (fun z => t*f z)) S) :
    (∀ x∈S,DifferentiableAt ℝ f x) ∧
      LipschitzOnWith (‖t⁻¹‖₊*K) (fderiv ℝ f) S := by
  have H (x:E) (hx:x∈S) := differentiableAt_of_const_mul ht (hd x hx)
  refine ⟨fun x hx => (H x hx).differentiableAt,?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [(H x hx).fderiv,(H y hy).fderiv,dist_eq_norm,←smul_sub,norm_smul]
  have HH := mul_le_mul_of_nonneg_left (hLip.dist_le_mul x hx y hy) (norm_nonneg t⁻¹)
  simpa only [dist_eq_norm,NNReal.coe_mul,coe_nnnorm,mul_assoc] using HH

end

open Set Filter MeasureTheory Metric
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma HasSecondTaylor.hasQuadraticExpansion {f : E → ℝ} {l : E →L[ℝ] ℝ}
    {B : E →L[ℝ] E →L[ℝ] ℝ} (hf : HasSecondTaylor f l B) :
    HasQuadraticExpansion f ((InnerProductSpace.toDual ℝ E).symm l) (bilinearOperator B) := by
  intro ε hε
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp (hf.eventually hε)
  refine ⟨r,hr,?_⟩
  intro h hh
  have H := hball (by simpa only [mem_ball,dist_zero_right] using hh)
  simpa only [quadraticTaylor,bilinearOperator_inner,InnerProductSpace.toDual_symm_apply,
    sub_add_eq_sub_sub] using H

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

lemma ae_secondTaylor_of_C11 {f : E → ℝ} {S : Set E} (hS : IsOpen S)
    (hd : ∀ x∈S,DifferentiableAt ℝ f x) {K : ℝ≥0}
    (hK : LipschitzOnWith K (fderiv ℝ f) S) :
    ∀ᵐ x ∂μ,x∈S → DifferentiableAt ℝ (fderiv ℝ f) x ∧
      HasSecondTaylor (fun h => f (x+h)) (fderiv ℝ f x)
        (fderiv ℝ (fderiv ℝ f) x) := by
  filter_upwards [hK.ae_differentiableWithinAt_of_mem (μ := μ)] with x hx hxS
  have H := (hx hxS).differentiableAt (hS.mem_nhds hxS)
  refine ⟨H,hasSecondTaylor_of_second_derivative ?_ H.hasFDerivAt⟩
  filter_upwards [hS.mem_nhds hxS] with y hy
  exact (hd y hy).hasFDerivAt

end WeakMTWTransport

end

end OAI
