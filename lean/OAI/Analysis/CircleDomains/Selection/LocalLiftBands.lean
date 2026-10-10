import OAI.Analysis.CircleDomains.Topology.CirclePartitionBands
import Mathlib.Topology.Order.LiminfLimsup

namespace OAI

/-! Local real lifts need only be bounded near the boundary point. Positive
smoothing contracts their limiting bands without choosing a global unit interval. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem local_band_inclusion_of_interval_preservation
    {X : Type*} (l : Filter X) [NeBot l] (u v : X → ℝ)
    (hul : IsBoundedUnder (· ≥ ·) l u) (huu : IsBoundedUnder (· ≤ ·) l u)
    (htransfer : ∀ a b : ℝ, (∀ᶠ y in l, u y ∈ Icc a b) →
      ∀ᶠ x in l, v x ∈ Icc a b) :
    liminf u l ≤ liminf v l ∧ limsup v l ≤ limsup u l := by
  obtain ⟨a, ha⟩ := hul.eventually_ge
  obtain ⟨b, hb⟩ := huu.eventually_le
  have huab : ∀ᶠ y in l, u y ∈ Icc a b := by
    filter_upwards [ha, hb] with y hya hyb
    exact ⟨hya, hyb⟩
  have hv := htransfer a b huab
  have hvl := isBoundedUnder_of_eventually_ge (hv.mono fun _ h => h.1)
  have hvu := isBoundedUnder_of_eventually_le (hv.mono fun _ h => h.2)
  constructor
  · apply (le_liminf_iff' hvu.isCoboundedUnder_ge hvl).2
    intro r hr
    have he : ∀ᶠ y in l, u y ∈ Icc r b := by
      filter_upwards [eventually_lt_of_lt_liminf hr hul, hb] with y hyr hyb
      exact ⟨hyr.le, hyb⟩
    exact (htransfer r b he).mono fun _ h => h.1
  · apply (limsup_le_iff' hvl.isCoboundedUnder_le hvu).2
    intro s hs
    have he : ∀ᶠ y in l, u y ∈ Icc a s := by
      filter_upwards [ha, eventually_lt_of_limsup_lt hs huu] with y hya hys
      exact ⟨hya, hys.le⟩
    exact (htransfer a s he).mono fun _ h => h.2

namespace OpenPlanePartition
variable {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} (ρ : OpenPlanePartition Ω ι)

 theorem adjustedCircleMix_band_inclusion
    (W : ι → Set EuclideanPlane) (hW : ∀ i, IsOpen (W i))
    (hconn : ∀ i, IsPreconnected (W i))
    (hsub : ∀ i, tsupport (ρ.weight i) ⊆ W i)
    (f : EuclideanPlane → UnitAddCircle) (u v : ι → EuclideanPlane → ℝ)
    (hu : ∀ i, ContinuousOn (u i) (W i))
    (hlift : ∀ i y, y ∈ W i → (u i y : UnitAddCircle) = f y)
    (hav : ∀ i, ∀ a b : ℝ, (∀ y ∈ W i, u i y ∈ Icc a b) →
      ∀ y ∈ tsupport (ρ.weight i), v i y ∈ Icc a b)
    {V : Set EuclideanPlane} (w : EuclideanPlane → ℝ) (hw : ContinuousOn w V)
    (hwlift : ∀ y ∈ V, (w y : UnitAddCircle) = f y)
    {s : EuclideanPlane} (hV : V ∈ 𝓝 s) (hs : s ∈ closure (Ω : Set EuclideanPlane))
    (hpatch : LocalPatchSupport (Ω : Set EuclideanPlane) ρ.weight W s)
    (hul : IsBoundedUnder (· ≥ ·) (𝓝[(Ω : Set EuclideanPlane)] s) w)
    (huu : IsBoundedUnder (· ≤ ·) (𝓝[(Ω : Set EuclideanPlane)] s) w) :
    liminf w (𝓝[(Ω : Set EuclideanPlane)] s) ≤
        liminf (ρ.adjustedCircleMix u v w) (𝓝[(Ω : Set EuclideanPlane)] s) ∧
      limsup (ρ.adjustedCircleMix u v w) (𝓝[(Ω : Set EuclideanPlane)] s) ≤
        limsup w (𝓝[(Ω : Set EuclideanPlane)] s) := by
  let : NeBot (𝓝[(Ω : Set EuclideanPlane)] s) := mem_closure_iff_nhdsWithin_neBot.mp hs
  apply local_band_inclusion_of_interval_preservation _ w _ hul huu
  intro a b hab
  exact ρ.adjustedCircleMix_eventual_interval W hW hconn hsub f u v hu hlift hav
    w hw hwlift hV hpatch hab

end OpenPlanePartition
end CircleDomainRigidity

end

end OAI
