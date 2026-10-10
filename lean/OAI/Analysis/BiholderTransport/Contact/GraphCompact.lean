import Mathlib
import OAI.Analysis.BiholderTransport.Contact.GraphProjection

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle
open Set

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Filter Set
open scoped Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped Topology

open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter
open scoped Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma isClosed_subgradientGraph {v : M → ℝ} (hv : Continuous v) :
    IsClosed (subgradientGraph (n := n) (cTransform v)) := by
  classical
  apply isOpen_compl_iff.mp
  apply isOpen_iff_mem_nhds.mpr
  rintro ⟨x,p⟩ hp
  have hn : p∉convexHull ℝ (activeLogs (n := n) v x) := by
    intro hh
    exact hp (active_hull_subset_normalSubdifferential hv x hh)
  have : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
    inferInstanceAs (FiniteDimensional ℝ (Model n))
  obtain ⟨f,K,hK,hpK⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ (activeLogs (n := n) v x))
    (isCompact_convexHull_finiteDimensional (isCompact_activeLogs (n := n) hv x)).isClosed hn
  let e := trivializationAt (Model n) (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) x
  have hx : x∈e.baseSet := mem_baseSet_trivializationAt _ _ x
  let g : Model n →L[ℝ] ℝ := f.comp (e.continuousLinearEquivAt ℝ x hx).symm.toContinuousLinearMap
  let F := fun z : TangentBundle 𝓘(ℝ,Model n) M => g (e z).2
  have hF (z : TangentBundle 𝓘(ℝ,Model n) M) (hz : z.1∈e.baseSet) : ContinuousAt F z :=
    g.continuous.continuousAt.comp ((e.toOpenPartialHomeomorph.continuousAt
      (e.mem_source.mpr hz)).snd)
  have hFx (q : TangentSpace 𝓘(ℝ,Model n) x) : F ⟨x,q⟩=f q := by
    dsimp only [F,g,ContinuousLinearMap.comp_apply]
    rw [e.apply_eq_prod_continuousLinearEquivAt ℝ x hx q]
    exact congrArg f ((e.continuousLinearEquivAt ℝ x hx).symm_apply_apply q)
  have HF : ∀ᶠ y in 𝓝 x, ∀ z : TangentBundle 𝓘(ℝ,Model n) M,
      z.2∈activeLogs (n := n) v z.1 → z.1=y → F z<K := by
    apply compact_eventually_fiberwise (isCompact_total_activeLogs hv)
      (FiberBundle.continuous_proj _ _) (continuousAt_id (x := x))
    rintro ⟨a,q⟩ hq he
    change a=x at he
    subst a
    have hqK : F ⟨x,q⟩<K := by rw [hFx]; exact hK q (subset_convexHull ℝ _ hq)
    have hsnd : ContinuousAt (fun a : M × TangentBundle 𝓘(ℝ,Model n) M => a.2)
        (x,⟨x,q⟩) := continuousAt_snd
    have hc : ContinuousAt (fun a : M × TangentBundle 𝓘(ℝ,Model n) M => F a.2)
        (x,⟨x,q⟩) := ContinuousAt.comp
          (f := fun a : M × TangentBundle 𝓘(ℝ,Model n) M => a.2)
          (g := F) (x := (x,⟨x,q⟩)) (hF ⟨x,q⟩ hx) hsnd
    exact hc.eventually_lt continuousAt_const hqK
  have hproj : Continuous (fun z : TangentBundle 𝓘(ℝ,Model n) M => z.1) :=
    FiberBundle.continuous_proj _ _
  have HK : ∀ᶠ z : TangentBundle 𝓘(ℝ,Model n) M in 𝓝 ⟨x,p⟩, K<F z :=
    continuousAt_const.eventually_lt (hF ⟨x,p⟩ hx) (by rw [hFx]; exact hpK)
  have HB : ∀ᶠ z : TangentBundle 𝓘(ℝ,Model n) M in 𝓝 ⟨x,p⟩, z.1∈e.baseSet :=
    hproj.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds hx)
  filter_upwards [hproj.continuousAt.eventually HF,HK,HB] with z hz hzK hzB
  intro hzG
  have hzh : z.2 ∈ convexHull ℝ (activeLogs (n := n) v z.1) :=
    normalSubdifferential_subset_active_hull hv z.1 hzG
  let L : TangentSpace 𝓘(ℝ,Model n) z.1 →L[ℝ] ℝ :=
    g.comp (e.continuousLinearMapAt ℝ z.1)
  have hLe (q : TangentSpace 𝓘(ℝ,Model n) z.1) : L q=F ⟨z.1,q⟩ := by
    dsimp only [L,F,ContinuousLinearMap.comp_apply]
    rw [Trivialization.continuousLinearMapAt_apply_of_mem ℝ e hzB]
  have hsub : activeLogs (n := n) v z.1 ⊆ {q | L q≤K} := by
    intro q hq
    rw [mem_ofPred_eq,hLe]
    exact (hz ⟨z.1,q⟩ hq rfl).le
  have hcv : Convex ℝ {q : TangentSpace 𝓘(ℝ,Model n) z.1 | L q≤K} :=
    convex_halfSpace_le L.toLinearMap.isLinear K
  have hbound := convexHull_min hsub hcv hzh
  change L z.2≤K at hbound
  rw [hLe] at hbound
  exact not_lt_of_ge hbound hzK

lemma isCompact_subgradientGraph {v : M → ℝ} (hv : Continuous v) :
    IsCompact (subgradientGraph (n := n) (cTransform v)) := by
  have : IsContinuousRiemannianBundle (Model n)
      (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) :=
    continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,Model n))
  apply (isCompact_bundle_disk (F := Model n)
    (E := fun x : M => TangentSpace 𝓘(ℝ,Model n) x) (Metric.diam (univ : Set M))).of_isClosed_subset
    (isClosed_subgradientGraph hv)
  intro z hz
  exact active_hull_norm_le_diam (normalSubdifferential_subset_active_hull hv z.1 hz)

end WeakMTWTransport

end

end OAI
