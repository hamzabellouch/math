import Mathlib
import OAI.Geometry.PrescribedPotential.NonlinearHessianCommutator

namespace OAI

/-! Sobolev Det Differential. -/

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

lemma determinant_map_contDiff (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) (n : ℕ) :
    ContDiff ℝ ∞ (D.determinant k hk n) := by
  change ContDiff ℝ ∞ (fun M : Fin n → Fin n → D.localizers.Sobolev (k : ℝ) =>
    D.determinant k hk n M)
  exact D.determinant_contDiff k hk n (fun i j (M : Fin n → Fin n → D.localizers.Sobolev (k : ℝ)) => M i j) (fun i j => by fun_prop)

def detDifferential (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) (n : ℕ)
    (M : Matrix (Fin n) (Fin n) (D.localizers.Sobolev (k : ℝ))) :
    (Fin n → Fin n → D.localizers.Sobolev (k : ℝ)) →L[ℝ] D.localizers.Sobolev (k : ℝ) :=
  fderiv ℝ (D.determinant k hk n) M

lemma detDifferential_contDiff (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) (n : ℕ) :
    ContDiff ℝ ∞ (D.detDifferential k hk n) := by
  exact (D.determinant_map_contDiff k hk n).fderiv_right (by simp)

lemma detDifferential_strong (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) (n : ℕ)
    (M N : Matrix (Fin n) (Fin n) (D.localizers.Sobolev (k : ℝ))) (x : X) :
    D.localizers.strong (k : ℝ) (D.detDifferential k hk n M N) x =
      NonlinearHessian.detDifferential
        (fun i j => D.localizers.strong (k : ℝ) (M i j) x)
        (fun i j => D.localizers.strong (k : ℝ) (N i j) x) := by
  let E : D.localizers.Sobolev (k : ℝ) →L[ℝ] ℂ :=
    (BoundedContinuousFunction.evalCLM ℝ x).comp (D.localizers.strong (k : ℝ))
  let EM : (Fin n → Fin n → D.localizers.Sobolev (k : ℝ)) →L[ℝ]
      (Fin n → Fin n → ℂ) := ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
        (E.comp (ContinuousLinearMap.proj j : (Fin n → D.localizers.Sobolev (k : ℝ)) →L[ℝ]
          D.localizers.Sobolev (k : ℝ))).comp (ContinuousLinearMap.proj i)
  have hleft := E.hasFDerivAt.comp M
    ((D.determinant_map_contDiff k hk n).differentiable (by simp) M).hasFDerivAt
  have hright := (NonlinearHessian.detDifferential_hasFDeriv (EM M)).comp M EM.hasFDerivAt
  have he : (fun u => E (D.determinant k hk n u)) = (fun u => Matrix.det (EM u)) := by
    funext u
    exact D.determinant_strong k hk n u x
  have hh := hleft.unique (hright.congr_of_eventuallyEq (Filter.Eventually.of_forall (congr_fun he)))
  exact congrArg (fun T : (Fin n → Fin n → D.localizers.Sobolev (k : ℝ)) →L[ℝ] ℂ => T N) hh

end GluingData
end GlobalElliptic

end
end

end OAI
