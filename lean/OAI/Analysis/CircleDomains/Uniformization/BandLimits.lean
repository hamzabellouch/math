import OAI.Analysis.CircleDomains.Selection.BandGraph
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Sequences

namespace OAI

/-!
# Identifying the band with the lower and upper boundary limits

This connects the compact graph construction to the manuscript's
definition of a real coordinate band by liminf and limsup on the
physical domain.
-/

open Set Filter
open scoped Topology

namespace CircleDomainRigidity

theorem mem_clusterGraph_iff_mapClusterPt
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {G : Set X} {f : X → ℝ} {x : X} {t : ℝ} :
    (x, t) ∈ clusterGraph G f ↔ MapClusterPt t (𝓝[G] x) f := by
  constructor
  · intro ht
    obtain ⟨z, hz, hzt⟩ := mem_closure_iff_seq_limit.mp ht
    let v : ℕ → X := fun n => (z n).1
    have hvG : ∀ n, v n ∈ G := by
      intro n
      obtain ⟨y, hy, heq⟩ := hz n
      simpa only [v, ← heq] using hy
    have hv : Tendsto v atTop (𝓝[G] x) :=
      tendsto_nhdsWithin_iff.mpr ⟨continuous_fst.tendsto (x, t) |>.comp hzt,
        Eventually.of_forall hvG⟩
    have hfz : Tendsto (f ∘ v) atTop (𝓝 t) := by
      convert continuous_snd.tendsto (x, t) |>.comp hzt using 1
      funext n
      obtain ⟨y, hy, heq⟩ := hz n
      simp only [Function.comp_apply, v, ← heq]
    exact hfz.mapClusterPt.of_comp hv
  · intro ht
    obtain ⟨v, hfv, hv⟩ := ht.exists_seq_tendsto
    have hpair : Tendsto (fun n => (v n, f (v n))) atTop (𝓝 (x, t)) :=
      (tendsto_nhdsWithin_iff.mp hv).1.prodMk_nhds hfv
    apply mem_closure_of_tendsto hpair
    filter_upwards [(tendsto_nhdsWithin_iff.mp hv).2] with n hn
    exact ⟨v n, hn, rfl⟩

theorem intervalFiberHull_clusterGraph_eq_boundary_band
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X] [CompactSpace X] [T2Space X]
    {G : Set X} {f : X → ℝ} {M : ℝ} (hM : ∀ x ∈ G, |f x| ≤ M)
    {x : X} (hx : x ∈ closure G) :
    {t : ℝ | (x, t) ∈ intervalFiberHull (clusterGraph G f)} =
      Icc (liminf f (𝓝[G] x)) (limsup f (𝓝[G] x)) := by
  let : NeBot (𝓝[G] x) := mem_closure_iff_nhdsWithin_neBot.mp hx
  have hbounds : ∀ᶠ y in 𝓝[G] x, -M ≤ f y ∧ f y ≤ M := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact abs_le.mp (hM y hy)
  have hlower : IsBoundedUnder (· ≥ ·) (𝓝[G] x) f :=
    isBoundedUnder_of_eventually_ge (hbounds.mono (fun _ hy => hy.1))
  have hupper : IsBoundedUnder (· ≤ ·) (𝓝[G] x) f :=
    isBoundedUnder_of_eventually_le (hbounds.mono (fun _ hy => hy.2))
  have hleast := isLeast_mapClusterPt_liminf hupper.isCoboundedUnder_ge hlower
  have hgreatest := isGreatest_mapClusterPt_limsup hlower.isCoboundedUnder_le hupper
  have heq : {t : ℝ | (x, t) ∈ clusterGraph G f} =
      {t | MapClusterPt t (𝓝[G] x) f} :=
    Set.ext (fun _ => mem_clusterGraph_iff_mapClusterPt)
  have hcompact := isCompact_real_fiber (isCompact_clusterGraph hM) x
  have hnonempty := clusterGraph_fiber_nonempty_of_mem_closure hM hx
  have hlo := hcompact.isLeast_sInf hnonempty
  have hhi := hcompact.isGreatest_sSup hnonempty
  rw [heq] at hlo hhi
  rw [intervalFiberHull_fiber_eq_Icc (isCompact_clusterGraph hM) x hnonempty]
  simpa only [heq] using congrArg₂ Icc (hlo.unique hleast) (hhi.unique hgreatest)

end CircleDomainRigidity

end OAI
