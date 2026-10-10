import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.TestProduct

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile189
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [SigmaFinite m] in
lemma IsLaplacian.mixed_pairing (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {u v A C ξ B : X → ℝ} (hu : IsLaplacian m u A) (hv : IsLaplacian m v C)
    (hξ : IsLaplacian m ξ B) {L M : ℝ≥0} (huL : LipschitzWith L u) (hvL : LipschitzWith M v)
    {Cu Cv Cξ : ℝ} (huB : ∀ x,|u x| ≤ Cu) (hvB : ∀ x,|v x| ≤ Cv)
    (hξB : ∀ᵐ x ∂m,|ξ x| ≤ Cξ) :
    2*(∫ x,ξ x*gamma m u v x ∂m) =
      (∫ x,u x*v x*B x ∂m)-(∫ x,A x*v x*ξ x ∂m)-(∫ x,u x*C x*ξ x ∂m) := by
  have hp := hu.mul_lipschitz hfin hpar hv huL hvL huB hvB
  have h1 := hp.2.2 ξ hξ.1
  have h2 := hξ.2.2 (fun x => u x*v x) hp.1
  have hc : (∫ x,gamma m (fun y => u y*v y) ξ x ∂m) =
      ∫ x,gamma m ξ (fun y => u y*v y) x ∂m := integral_congr_ae (gamma_comm _ _)
  have i1 : Integrable (fun x => A x*v x*ξ x) m :=
    (memLp_mul_bounded hu.2.1 hvL.continuous.aestronglyMeasurable (ae_of_all _ hvB)).integrable_mul hξ.1.1
  have i2 : Integrable (fun x => u x*C x*ξ x) m := by
    have H := (memLp_mul_bounded hv.2.1 huL.continuous.aestronglyMeasurable (ae_of_all _ huB)).integrable_mul hξ.1.1
    change Integrable (fun x => C x*u x*ξ x) m at H
    simpa only [mul_comm (C _)] using H
  have ig := integrable_bounded_gamma hfin hu.1 hv.1 hξ.1.1.aestronglyMeasurable hξB
  have he : (∫ x,(A x*v x+C x*u x+2*gamma m u v x)*ξ x ∂m) =
      (∫ x,A x*v x*ξ x ∂m)+(∫ x,u x*C x*ξ x ∂m)+2*(∫ x,ξ x*gamma m u v x ∂m) := by
    calc
      _ = ∫ x,(A x*v x*ξ x+u x*C x*ξ x)+2*(ξ x*gamma m u v x) ∂m := by
        congr 1; funext x; ring
      _ = _ := by
        rw [integral_add (f := fun x => A x*v x*ξ x+u x*C x*ξ x) (i1.add i2) (ig.const_mul 2),
          integral_add i1 i2,integral_const_mul]
  have he' : (∫ x,B x*(u x*v x) ∂m) = ∫ x,u x*v x*B x ∂m := by
    congr 1; funext x; ring
  rw [he] at h1
  rw [he'] at h2
  linarith

omit [SigmaFinite m] in
lemma IsLaplacian.square_gamma_pairing (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {u A ξ B : X → ℝ}
    (hu : IsLaplacian m u A) (hξ : IsLaplacian m ξ B)
    {L : ℝ≥0} (huL : LipschitzWith L u) {Cu Cξ : ℝ}
    (huB : ∀ x,|u x| ≤ Cu) (hξB : ∀ᵐ x ∂m,|ξ x| ≤ Cξ) :
    (∫ x,ξ x*gamma m u u x ∂m) =
      (1/2)*(∫ x,(u x)^2*B x ∂m)-(∫ x,u x*A x*ξ x ∂m) := by
  have H := hu.mixed_pairing hfin hpar hu hξ huL huL huB huB hξB
  have e1 : (∫ x,u x*u x*B x ∂m) = ∫ x,(u x)^2*B x ∂m := by simp only [pow_two]
  have e2 : (∫ x,A x*u x*ξ x ∂m) = ∫ x,u x*A x*ξ x ∂m := by congr 1; funext x; ring
  rw [e1,e2] at H
  linarith
end WeakHessian

end
end InlinedFile189

end OAI
