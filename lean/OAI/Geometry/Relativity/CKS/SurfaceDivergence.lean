import OAI.Geometry.Relativity.CKS.SchwarzschildMetric
import OAI.Geometry.Relativity.CKS.SchwarzschildHorizonExclusionDefinitions
import OAI.Geometry.Relativity.CKS.MetricPairDerivative

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface

lemma christoffel_metric_compatibility
    (g : E3 → E3 →L[ℝ] E3 →L[ℝ] ℝ)
    (hs : ∀ x a b, g x a b = g x b a) (x a b c : E3) :
    christoffelPair g x a b c + christoffelPair g x a c b =
      fderiv ℝ (fun z => g z b c) x a := by
  have hsym (u v : E3) : (fun z => g z u v) = (fun z => g z v u) := funext (fun z => hs z u v)
  dsimp [christoffelPair]
  rw [hsym c b]
  ring

def parameterNormalDerivative (m : ℝ) (f N : E2 → E3) (y a b : E2) : ℝ :=
  cartMetric m (f y) (fderiv ℝ N y a) (fderiv ℝ f y b) +
    christoffelPair (cartMetric m) (f y) (fderiv ℝ f y a) (N y) (fderiv ℝ f y b)

lemma parameterSecondForm_eq_normalDerivative {m : ℝ} (hm : 0 < m)
    {f N : E2 → E3} {y : E2} (hr : 2*m ≤ ‖f y‖)
    (hf : ContDiffAt ℝ ∞ f y) (hN : DifferentiableAt ℝ N y)
    (horth : ∀ᶠ z in 𝓝 y, ∀ b, cartMetric m (f z) (N z) (fderiv ℝ f z b) = 0)
    (a b : E2) :
    parameterSecondForm m f y (N y) a b = parameterNormalDerivative m f N y a b := by
  have hg := (cartMetric_smoothAt hm hr).differentiableAt (by simp)
  have hdf : DifferentiableAt ℝ (fun z => fderiv ℝ f z b) y :=
    ((hf.fderiv_right (by simp : ∞+1 ≤ ∞)).clm_apply contDiffAt_const).differentiableAt (by simp)
  have he : (fun z => cartMetric m (f z) (N z) (fderiv ℝ f z b)) =ᶠ[𝓝 y] (fun _ => (0:ℝ)) :=
    horth.mono (fun z hz => hz b)
  have hz := congrArg (fun L : E2 →L[ℝ] ℝ => L a) he.fderiv_eq
  rw [metric_pair_derivative_general _ hg (hf.differentiableAt (by simp)) hN hdf] at hz
  simp only [fderiv_const_apply,zero_apply] at hz
  have hc := christoffel_metric_compatibility (cartMetric m) (cartMetric_symm m)
    (f y) (fderiv ℝ f y a) (N y) (fderiv ℝ f y b)
  dsimp [parameterSecondForm,parameterNormalDerivative]
  linarith

def parameterDivergence (m : ℝ) (f N : E2 → E3) (y : E2) : ℝ :=
  let a := firstFrame (cartMetric m (f y)) (fderiv ℝ f y)
  let b := secondFrame (cartMetric m (f y)) (fderiv ℝ f y)
  parameterNormalDerivative m f N y a a + parameterNormalDerivative m f N y b b

lemma parameterMeanCurvature_eq_divergence {m : ℝ} (hm : 0 < m)
    {f N : E2 → E3} {y : E2} (hr : 2*m ≤ ‖f y‖)
    (hf : ContDiffAt ℝ ∞ f y) (hN : DifferentiableAt ℝ N y)
    (horth : ∀ᶠ z in 𝓝 y, ∀ b, cartMetric m (f z) (N z) (fderiv ℝ f z b) = 0) :
    parameterMeanCurvature m f y (N y) = parameterDivergence m f N y := by
  simp only [parameterMeanCurvature,parameterDivergence,
    parameterSecondForm_eq_normalDerivative hm hr hf hN horth]

end CKSSchwarzschild

end

end OAI
