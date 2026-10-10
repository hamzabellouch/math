import Mathlib
import OAI.Geometry.PrescribedPotential.NonlinearHessianCommutator
import OAI.Geometry.PrescribedPotential.NonlinearRemainder

namespace OAI

/-! Nonlinear Remainder Strong. -/

section

 

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff Classical Matrix.Norms.Elementwise
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

lemma nonlinearRemainder_strong_embed (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (p : ι) (v : EC d) (f : Smooth A) (x : X) :
    D.localizers.strong (k : ℝ)
      (D.nonlinearRemainder k hk p v (D.localizers.embed ((k : ℝ)+2) f)) x =
      D.regularityInverseDet p x *
        NonlinearHessian.detDifferential
          (fun i j => D.regularityMetric p i j x + D.regularityHessian p i j f x)
          (fun i j => D.regularityError p v i j f x -
            D.localizedDerivative p v (D.regularityMetric p i j) x) -
      D.localizedDerivative p v (D.regularityInverseDet p) x *
        Matrix.det (fun i j => D.regularityMetric p i j x + D.regularityHessian p i j f x) := by
  have hs : (Module.finrank ℝ (EC d) : ℝ) < 2*(k : ℝ) := by
    have hh : (Module.finrank ℝ (EC d) : ℝ) < (k : ℝ) := by exact_mod_cast hk
    linarith [Nat.cast_nonneg (α := ℝ) k]
  simp only [nonlinearRemainder,map_sub,BoundedContinuousFunction.sub_apply,
    D.product_strong,BoundedContinuousFunction.mul_apply,D.localizers.strong_embed _ hs]
  erw [D.detDifferential_strong,D.determinant_strong]
  have hM : (fun (i j : Fin d) => D.localizers.strong (k : ℝ)
      (D.regularityMatrix k p (D.localizers.embed ((k : ℝ)+2) f) i j) x) =
      (fun i j => D.regularityMetric p i j x + D.regularityHessian p i j f x) := by
    funext i j
    simp only [regularityMatrix,D.completedRegularityHessian_embed,map_add,
      BoundedContinuousFunction.add_apply,D.localizers.strong_embed _ hs]
    rfl
  have hE : (fun (i j : Fin d) => D.localizers.strong (k : ℝ)
      (D.regularityErrorMatrix k p v (D.localizers.embed ((k : ℝ)+2) f) i j) x) =
      (fun i j => D.regularityError p v i j f x -
        D.localizedDerivative p v (D.regularityMetric p i j) x) := by
    funext i j
    simp only [regularityErrorMatrix,D.completedRegularityError_embed,map_sub,
      BoundedContinuousFunction.sub_apply,D.localizers.strong_embed _ hs]
    rfl
  rw [hM,hE]
  rfl

end GluingData
end GlobalElliptic

end
end

end OAI
