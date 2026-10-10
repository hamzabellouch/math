import OAI.Analysis.CircleDomains.Uniformization.GeometricUniformLimit
import Mathlib.Topology.MetricSpace.HausdorffDistance

namespace OAI

/-! Exact fiber identities and surjectivity for limits of homeomorphisms. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma surjective_uniform_limit {X Y : Type*}
    [TopologicalSpace X] [CompactSpace X] [MetricSpace Y]
    {f : X → Y} (hf : Continuous f) (F : ℕ → X → Y)
    (hF : ∀ n, Surjective (F n)) (hlim : TendstoUniformly F f atTop) :
    Surjective f := by
  intro y
  have hy : y ∈ closure (range f) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨n,hn⟩ := (Metric.tendstoUniformly_iff.mp hlim ε hε).exists
    obtain ⟨x,hx⟩ := hF n y
    exact ⟨f x,mem_range_self x,by simpa only [hx,dist_comm] using hn x⟩
  rw [(isCompact_range hf).isClosed.closure_eq] at hy
  exact hy

lemma uniform_limit_inverse_observation {X Y Z : Type*}
    [TopologicalSpace X] [MetricSpace Y] [MetricSpace Z]
    (H : ℕ → (X ≃ₜ Y)) (q : X → Z)
    {f : X → Y} {g : Y → Z}
    (hg : Continuous g)
    (hf : TendstoUniformly (fun n => H n) f atTop)
    (hginv : TendstoUniformly (fun n y => q ((H n).symm y)) g atTop) :
    ∀ x, g (f x)=q x := by
  intro x
  have h := hginv.tendsto_comp hg.continuousAt (hf.tendsto_at x)
  simp only [Homeomorph.symm_apply_apply] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

lemma uniform_limit_eq_of_shrinking_distance {X Y : Type*} [MetricSpace Y]
    {F : ℕ → X → Y} {f : X → Y} (hf : TendstoUniformly F f atTop)
    {x y : X} (hsmall : ∀ n, dist (F n x) (F n y)≤componentShrinkRadius n) :
    f x=f y := by
  apply dist_eq_zero.mp
  apply le_antisymm _ dist_nonneg
  apply le_of_tendsto_of_tendsto ((hf.tendsto_at x).dist (hf.tendsto_at y))
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2)
      (by norm_num : (1/2:ℝ)<1))
  exact Eventually.of_forall hsmall

end CircleDomainRigidity

end

end OAI
