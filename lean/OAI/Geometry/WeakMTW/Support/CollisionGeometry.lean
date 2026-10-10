import Mathlib
import OAI.Geometry.WeakMTW.Variations.ActionBranch

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

omit [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M] in
 theorem mulState_injective {s : ℝ} (hs : s ≠ 0) :
    Function.Injective (mulState (E := Model n) (M := M) s) := by
  intro p q he
  have hi := congrArg (mulState s⁻¹) he
  change (⟨p.1, s⁻¹ • (s • p.2)⟩ : TangentBundle (model n) M) =
    (⟨q.1, s⁻¹ • (s • q.2)⟩ : TangentBundle (model n) M) at hi
  simpa only [inv_smul_smul₀ hs] using hi

 theorem branch_collision_base_ne {x z : M} (B : ActionBranch (n := n) x z)
    {p q : TangentBundle (model n) M} {s : ℝ} (hs : s ≠ 0)
    (hp : mulState s p ∈ (stateChart x).source)
    (hq : mulState s q ∈ (stateChart x).source)
    (hpB : stateChart x (mulState s p) ∈ B.coord.source)
    (hqB : stateChart x (mulState s q) ∈ B.coord.source)
    (he : exp p.1 (s•p.2) = exp q.1 (s•q.2)) (hne : p ≠ q) : p.1 ≠ q.1 := by
  intro hb
  apply hne
  apply mulState_injective hs
  apply (stateChart x).injOn hp hq
  apply B.coord.injOn hpB hqB
  rw [B.map_eq, pairExpCoordinates_state x z _ hp, pairExpCoordinates_state x z _ hq]
  simp only [mulState]
  exact Prod.ext (congrArg (chartAt (Model n) x) hb) (congrArg (chartAt (Model n) z) he)

 theorem ActionBranch.eq_cost_along {x z : M} (B : ActionBranch (n := n) x z)
    {v : TangentSpace (model n) x} (hv : v ∈ injectivityDomain x)
    (he : stateChart x (⟨x,v⟩ : TangentBundle (model n) M) ∈ B.coord.source)
    {p q : ℕ → M} (hp : Tendsto p atTop (𝓝 x)) (hq : Tendsto q atTop (𝓝 (exp x v)))
    (hz : exp x v ∈ (chartAt (Model n) z).source) :
    ∀ᶠ j in atTop, B.value (chartAt (Model n) x (p j),chartAt (Model n) z (q j)) = cost (p j) (q j) := by
  have hc := ((chartAt (Model n) x).continuousAt (mem_chart_source (Model n) x)).tendsto.comp hp
  have hd := ((chartAt (Model n) z).continuousAt hz).tendsto.comp hq
  have hh := (hc.prodMk_nhds hd) (B.eq_cost_near hv hz he)
  have hpS := hp ((chartAt (Model n) x).open_source.mem_nhds (mem_chart_source (Model n) x))
  have hqS := hq ((chartAt (Model n) z).open_source.mem_nhds hz)
  filter_upwards [hh,hpS,hqS] with j hj hjp hjq
  change B.value (chartAt (Model n) x (p j),chartAt (Model n) z (q j)) =
    cost ((chartAt (Model n) x).symm (chartAt (Model n) x (p j)))
      ((chartAt (Model n) z).symm (chartAt (Model n) z (q j))) at hj
  simpa only [(chartAt (Model n) x).left_inv hjp,(chartAt (Model n) z).left_inv hjq] using hj

omit [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M] in
 theorem bundle_base_limit {p : ℕ → TangentBundle (model n) M} {p₀ : TangentBundle (model n) M}
    (hp : Tendsto p atTop (𝓝 p₀)) : Tendsto (fun j => (p j).1) atTop (𝓝 p₀.1) :=
  (FiberBundle.continuous_proj (Model n) (TangentSpace (model n))).continuousAt.tendsto.comp hp

 theorem bundle_endpoint_limit {p : ℕ → TangentBundle (model n) M} {p₀ : TangentBundle (model n) M}
    (hp : Tendsto p atTop (𝓝 p₀)) :
    Tendsto (fun j => exp (p j).1 (p j).2) atTop (𝓝 (exp p₀.1 p₀.2)) :=
  exp_total_smooth.continuous.continuousAt.tendsto.comp hp

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
