import Mathlib
import OAI.Geometry.WeakMTW.Variations.RadialHessianCalculus

namespace OAI

namespace WeakMTWGlobalSupport

section

open Filter Set
open scoped Topology ContDiff
namespace RadialHessianCalculus
open CoordinateGeometry
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

 def actionForm (G : E → MetricTensor E) (f : E → ℝ) (a ν : E) : LinearMap.BilinForm ℝ E :=
  LinearMap.mk₂ ℝ (fun v w => fderiv ℝ (fderiv ℝ f) a v w +
    lowerChristoffel (fderiv ℝ G a) v w ν)
    (by intro v v' w; simp only [lowerChristoffel_apply,map_add,add_apply]; ring)
    (by intro c v w; simp only [lowerChristoffel_apply,map_smul,smul_apply,smul_eq_mul]; ring)
    (by intro v w w'; simp only [lowerChristoffel_apply,map_add,add_apply]; ring)
    (by intro c v w; simp only [lowerChristoffel_apply,map_smul,smul_apply,smul_eq_mul]; ring)

 theorem actionForm_eq (G : E → MetricTensor E) (f : E → ℝ) (a ν v w : E)
    (hpos : ∀ z : E, z ≠ 0 → 0 < G a z z)
    (hsymm : ∀ z z', G a z z' = G a z' z) :
    actionForm G f a ν v w = fderiv ℝ (fderiv ℝ f) a v w +
      G a ν (christoffel G a v w) := by
  change _ + lowerChristoffel (fderiv ℝ G a) v w ν = _
  rw [hsymm ν,metric_christoffel hpos,lowerChristoffel_apply]

 omit [FiniteDimensional ℝ E] in
 theorem actionForm_symmetric (G : E → MetricTensor E) (f : E → ℝ)
    {S : Set E} (hS : IsOpen S) (hG : DifferentiableOn ℝ G S)
    (hsym : ∀ r ∈ S, ∀ v w, G r v w = G r w v)
    {a : E} (ha : a ∈ S) (hf : ContDiffAt ℝ 2 f a) (ν v w : E) :
    actionForm G f a ν v w = actionForm G f a ν w v := by
  change _ + lowerChristoffel (fderiv ℝ G a) v w ν =
    _ + lowerChristoffel (fderiv ℝ G a) w v ν
  rw [(hf.isSymmSndFDerivAt (by norm_num)).eq v w]
  simp only [lowerChristoffel_apply,derivative_metric_symmetric hS hG hsym ha ν v w]
  ring

 theorem actionForm_radial (G : E → MetricTensor E) (ν : E → E) (f : E → ℝ)
    {S : Set E} (hS : IsOpen S) (hG : DifferentiableOn ℝ G S)
    (hsym : ∀ r ∈ S, ∀ v w, G r v w = G r w v)
    {a : E} (ha : a ∈ S) (hpos : ∀ v : E, v ≠ 0 → 0 < G a v v)
    (hν : DifferentiableAt ℝ ν a) (hf : ContDiffAt ℝ 2 f a)
    (henergy : f =ᶠ[𝓝 a] (fun r => G r (ν r) (ν r) / 2))
    (hgrad : ∀ᶠ r in 𝓝 a, ∀ w, fderiv ℝ f r w = -G r (ν r) w) (ξ : E) :
    actionForm G f a (ν a) ξ (ν a) = G a ξ (ν a) := by
  rw [actionForm_eq G f a (ν a) ξ (ν a) hpos (hsym a ha)]
  exact covariant_radial G ν f hS hG hsym ha hpos hν hf henergy hgrad ξ

end
end RadialHessianCalculus
end

end WeakMTWGlobalSupport

end OAI
