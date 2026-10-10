import Mathlib
import OAI.Geometry.WeakMTW.Variations.GeneratingTrial

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace GeneratingCalculus
 theorem positive_of_trial {H U R P : ℝ} (hP : 0 ≤ P) (hR : R ≠ 0)
    (h : ∀ a : ℝ, H ≤ U + 2*a*R+a^2*P) : 0 < P := by
  by_contra hn
  have hzero : P = 0 := le_antisymm (le_of_not_gt hn) hP
  have hh := h ((H-U-1)/(2*R))
  rw [hzero,mul_zero,add_zero] at hh
  have heq : U+2*((H-U-1)/(2*R))*R = H-1 := by field_simp; ring
  rw [heq] at hh
  linarith

 theorem bilinear_quadratic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : E →L[ℝ] E →L[ℝ] ℝ) (A K : E) (α : ℝ)
    (h : Q K A = Q A K) :
    Q (A+α•K) (A+α•K) = Q A A+2*α*Q A K+α^2*Q K K := by
  simp only [map_add,map_smul,add_apply,smul_apply,smul_eq_mul]
  rw [h]
  ring
end GeneratingCalculus

namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry DiscreteVariational RadialHessianCalculus
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem generating_scalar_trial (x y : M) {ε : ℝ} (hε : 0 < ε) (hε₁ : ε < 1)
    {v : TangentSpace (model n) x} (hv : v ∈ injectivityDomain x)
    (hq : GeneratingChartAction x y ε (stateChart x (⟨x,v⟩ : TangentBundle (model n) M)))
    (ξ : TangentSpace (model n) x) (κ : Model n) (α : ℝ) :
    actionHessian x v ξ ξ ≤
      (generatingHessian x y ε (stateChart x (⟨x,v⟩ : TangentBundle (model n) M))
        ((tangentChartLinear x ξ,0),0) ((tangentChartLinear x ξ,0),0) +
      lowerChristoffel (fderiv ℝ (metric x) (chartAt (Model n) x x))
        (tangentChartLinear x ξ) (tangentChartLinear x ξ) (tangentChartLinear x v)) +
      2*α*generatingHessian x y ε (stateChart x (⟨x,v⟩ : TangentBundle (model n) M))
        ((tangentChartLinear x ξ,0),0) ((0,κ),0) +
      α^2*generatingHessian x y ε (stateChart x (⟨x,v⟩ : TangentBundle (model n) M))
        ((0,κ),0) ((0,κ),0) := by
  have ht := generating_action_trial x y hε hε₁ hv hq ξ κ α
  let A : (Model n × Model n) × Model n := ((tangentChartLinear x ξ,0),0)
  let K : (Model n × Model n) × Model n := ((0,κ),0)
  have he : ((tangentChartLinear x ξ,α•κ),0) = A+α•K := by simp [A,K]
  rw [he] at ht
  rw [GeneratingCalculus.bilinear_quadratic _ A K α (generatingHessian_symmetric x y hq K A)] at ht
  dsimp only [A,K] at ht
  linarith only [ht]

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
