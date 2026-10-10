import Mathlib
import OAI.Geometry.WeakMTW.Coordinates.TangentCoordinates

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace RiemannianLocal
noncomputable section
open ChartMetric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]

 theorem stateChart_pairing (x y : M) (hy : y ∈ (chartAt E x).source)
    (v w : TangentSpace 𝓘(ℝ, E) y) :
    metric x (chartAt E x y) (stateChart x ⟨y,v⟩).2 (stateChart x ⟨y,w⟩).2 = inner ℝ v w := by
  let e := trivializationAt E (TangentSpace 𝓘(ℝ, E)) x
  have hb : y ∈ e.baseSet := by simpa only [e,TangentBundle.trivializationAt_baseSet] using hy
  rw [metric_apply]
  change inner ℝ (e.symmL ℝ ((chartAt E x).symm (chartAt E x y)) (e ⟨y,v⟩).2)
    (e.symmL ℝ ((chartAt E x).symm (chartAt E x y)) (e ⟨y,w⟩).2) = inner ℝ v w
  rw [(chartAt E x).left_inv hy]
  simp only [e.symmL_apply hb, e.symm_apply_apply_mk hb]

 omit [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)] in
 theorem curveState_chart_deriv' (x : M) {γ : ℝ → M} {a : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ a)
    (ha : γ a ∈ (chartAt E x).source) :
    deriv ((chartAt E x) ∘ γ) a = (stateChart x (curveState (E := E) γ a)).2 := by
  rw [curveState_chart_deriv x hγ ha, tangentMap_chart (p := (⟨x,0⟩ : TangentBundle 𝓘(ℝ, E) M)) ha]
  rfl

 theorem metric_chart_pair (x y : M) (hy : y ∈ (chartAt E x).source)
    (v w : TangentSpace 𝓘(ℝ, E) y) :
    metric x (chartAt E x y) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E x) y v)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E x) y w) = inner ℝ v w := by
  have hv := congrArg (fun p : TangentBundle 𝓘(ℝ, E) E => p.2)
    (tangentMap_chart (p := (⟨x,0⟩ : TangentBundle 𝓘(ℝ, E) M))
      (q := (⟨y,v⟩ : TangentBundle 𝓘(ℝ, E) M)) hy)
  have hw := congrArg (fun p : TangentBundle 𝓘(ℝ, E) E => p.2)
    (tangentMap_chart (p := (⟨x,0⟩ : TangentBundle 𝓘(ℝ, E) M))
      (q := (⟨y,w⟩ : TangentBundle 𝓘(ℝ, E) M)) hy)
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E x) y v = (stateChart x ⟨y,v⟩).2 at hv
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E x) y w = (stateChart x ⟨y,w⟩).2 at hw
  rw [hv,hw,stateChart_pairing x y hy]

end
end RiemannianLocal
end

end WeakMTWGlobalSupport

end OAI
