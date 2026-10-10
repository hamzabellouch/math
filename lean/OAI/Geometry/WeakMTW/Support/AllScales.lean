import Mathlib
import OAI.Geometry.WeakMTW.Support.FirstScale
import OAI.Geometry.WeakMTW.Support.InteriorCharacterization
import OAI.Geometry.WeakMTW.Support.ActiveContinuation

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]
  {ι : Type*} [Fintype ι] [Nonempty ι]

 theorem activeHull_scaled_mem_injectivity (hMTW : HasWeakMTW (n := n) (M := M))
     (y : ι → M) (h : ι → ℝ) {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
     (x : M) {b : TangentSpace (model n) x} (hb : b ∈ activeHull y h x) :
     t•b ∈ injectivityDomain x := by
   by_contra hfail
   obtain ⟨s,hs,hst,hbelow,hmin,p,hp,hbad⟩ := compact_first_scale
     (activeHullGraph_compact y h) ht (p₀ := ⟨x,b⟩) hb hfail
   have hs1 := hst.trans_lt ht1
   have hbij := activeProjection_critical_bijective y h hMTW hs hs1 hbelow hmin
   have hn := activeHull_critical_nonconjugate hMTW y h hs.le hs1
     (fun x a ha => hmin ⟨x,a⟩ ha) p.1 (b := p.2) hp
   apply hbad
   apply unique_nonconjugate_mem_injectivity hn
   intro w hw he
   exact activeProjection_injective_unique y h hs hbij.1 hp hw he

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
