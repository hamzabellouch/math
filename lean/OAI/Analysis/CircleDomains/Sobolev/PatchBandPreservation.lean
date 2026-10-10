import OAI.Analysis.CircleDomains.Sobolev.PositiveLocalAverages
import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.MetricSpace.HausdorffDistance

namespace OAI

/-! Positive partition sums preserve every boundary band when all active
sampling patches shrink towards that boundary point. -/

open Set Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {X ι : Type*}

section Topological
variable [TopologicalSpace X]

def LocalPatchSupport (G : Set X) (w : ι → X → ℝ) (W : ι → Set X) (s : X) : Prop :=
  ∀V ∈ 𝓝 s, ∀ᶠ x in 𝓝[G] s, ∀i, w i x ≠ 0 → W i ⊆ G ∩ V

theorem positive_patch_eventual_bounds
    (G : Set X) (w v : ι → X → ℝ) (W : ι → Set X) (u : X → ℝ)
    (hw : ∀i x, 0 ≤ w i x) (hsum : ∀x ∈ G, ∑ᶠ i, w i x = 1)
    (hav : ∀i x, x ∈ G → w i x ≠ 0 → ∀a b : ℝ,
      (∀y ∈ W i, u y ∈ Icc a b) → v i x ∈ Icc a b)
    {s : X} (hs : LocalPatchSupport G w W s) {a b : ℝ}
    (hab : ∀ᶠ y in 𝓝[G] s, u y ∈ Icc a b) :
    ∀ᶠ x in 𝓝[G] s, (∑ᶠ i, w i x * v i x) ∈ Icc a b := by
  obtain ⟨V, hV, hsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hab
  filter_upwards [self_mem_nhdsWithin, hs V hV] with x hx hpatch
  simpa only [smul_eq_mul] using (convex_Icc a b).finsum_mem
    (fun i => hw i x) (hsum x hx) (fun i hi => hav i x hx hi a b
      (fun y hy => hsub ⟨(hpatch i hi hy).2, (hpatch i hi hy).1⟩))

theorem band_inclusion_of_eventual_interval_preservation
    (G : Set X) (u v : X → ℝ) {s : X} (hGs : s ∈ closure G)
    (hb : ∀x, u x ∈ Icc 0 1)
    (htransfer : ∀a b : ℝ, (∀ᶠ y in 𝓝[G] s, u y ∈ Icc a b) →
      ∀ᶠ x in 𝓝[G] s, v x ∈ Icc a b) :
    liminf u (𝓝[G] s) ≤ liminf v (𝓝[G] s) ∧
      limsup v (𝓝[G] s) ≤ limsup u (𝓝[G] s) := by
  let : NeBot (𝓝[G] s) := mem_closure_iff_nhdsWithin_neBot.mp hGs
  have hv := htransfer 0 1 (Eventually.of_forall hb)
  have hul : IsBoundedUnder (· ≥ ·) (𝓝[G] s) u :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall fun x => (hb x).1)
  have huu : IsBoundedUnder (· ≤ ·) (𝓝[G] s) u :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall fun x => (hb x).2)
  have hvl : IsBoundedUnder (· ≥ ·) (𝓝[G] s) v :=
    isBoundedUnder_of_eventually_ge (hv.mono fun _ h => h.1)
  have hvu : IsBoundedUnder (· ≤ ·) (𝓝[G] s) v :=
    isBoundedUnder_of_eventually_le (hv.mono fun _ h => h.2)
  constructor
  · apply (le_liminf_iff' hvu.isCoboundedUnder_ge hvl).2
    intro a ha
    have he : ∀ᶠ y in 𝓝[G] s, u y ∈ Icc a 1 := by
      filter_upwards [eventually_lt_of_lt_liminf ha hul] with y hy
      exact ⟨hy.le, (hb y).2⟩
    exact (htransfer a 1 he).mono fun _ h => h.1
  · apply (limsup_le_iff' hvl.isCoboundedUnder_le hvu).2
    intro b hb'
    have he : ∀ᶠ y in 𝓝[G] s, u y ∈ Icc 0 b := by
      filter_upwards [eventually_lt_of_limsup_lt hb' huu] with y hy
      exact ⟨(hb y).1, hy.le⟩
    exact (htransfer 0 b he).mono fun _ h => h.2

theorem positive_patch_band_inclusion
    (G : Set X) (w v : ι → X → ℝ) (W : ι → Set X) (u : X → ℝ)
    (hw : ∀i x, 0 ≤ w i x) (hsum : ∀x ∈ G, ∑ᶠ i, w i x = 1)
    (hav : ∀i x, x ∈ G → w i x ≠ 0 → ∀a b : ℝ,
      (∀y ∈ W i, u y ∈ Icc a b) → v i x ∈ Icc a b)
    {s : X} (hGs : s ∈ closure G) (hb : ∀x, u x ∈ Icc 0 1)
    (hs : LocalPatchSupport G w W s) :
    liminf u (𝓝[G] s) ≤ liminf (fun x => ∑ᶠ i, w i x * v i x) (𝓝[G] s) ∧
      limsup (fun x => ∑ᶠ i, w i x * v i x) (𝓝[G] s) ≤ limsup u (𝓝[G] s) :=
  band_inclusion_of_eventual_interval_preservation G u _ hGs hb
    (fun _ _ => positive_patch_eventual_bounds G w v W u hw hsum hav hs)

end Topological

section Metric
variable [MetricSpace X]

theorem localPatchSupport_of_tendsto_radius
    (G : Set X) (w : ι → X → ℝ) (W : ι → Set X) (r : X → ℝ) {s : X}
    (hr : Tendsto r (𝓝[G] s) (𝓝 0))
    (hW : ∀x ∈ G, ∀i, w i x ≠ 0 → ∀y ∈ W i, y ∈ G ∧ dist y x ≤ r x) :
    LocalPatchSupport G w W s := by
  intro V hV
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hV
  have hr' := (tendsto_order.mp hr).2 (ε / 2) (half_pos hε)
  have hx' : ∀ᶠ x in 𝓝[G] s, dist x s < ε / 2 :=
    nhdsWithin_le_nhds (ball_mem_nhds s (half_pos hε))
  filter_upwards [self_mem_nhdsWithin, hr', hx'] with x hx hrx hxs i hi y hy
  obtain ⟨hyG, hyx⟩ := hW x hx i hi y hy
  refine ⟨hyG, hball ?_⟩
  change dist y s < ε
  linarith [dist_triangle y x s]

theorem localPatchSupport_of_dust_distance
    (G B : Set X) (w : ι → X → ℝ) (W : ι → Set X) {C : ℝ} {s : X}
    (hs : s ∈ B)
    (hW : ∀x ∈ G, ∀i, w i x ≠ 0 → ∀y ∈ W i,
      y ∈ G ∧ dist y x ≤ C * infDist x B) : LocalPatchSupport G w W s := by
  apply localPatchSupport_of_tendsto_radius G w W (fun x => C * infDist x B) _ hW
  have h : Tendsto (fun x => infDist x B) (𝓝[G] s) (𝓝 (infDist s B)) :=
    ((continuous_infDist_pt B).tendsto s).mono_left nhdsWithin_le_nhds
  simpa only [infDist_zero_of_mem hs, mul_zero] using tendsto_const_nhds.mul h

end Metric
end CircleDomainRigidity

end

end OAI
