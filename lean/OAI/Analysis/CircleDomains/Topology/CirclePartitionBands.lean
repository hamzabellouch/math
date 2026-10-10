import OAI.Analysis.CircleDomains.Sobolev.CirclePartitionSmoothing
import OAI.Analysis.CircleDomains.Sobolev.PatchBandPreservation

namespace OAI

/-! Positive smoothing of local circle branches preserves the limiting
bands in every comparison branch. Connected sampling patches fix the
integer transition before averaging. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
namespace OpenPlanePartition

variable {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} (ρ : OpenPlanePartition Ω ι)

 def adjustedCircleMix (u v : ι → EuclideanPlane → ℝ) (w : EuclideanPlane → ℝ)
    (x : EuclideanPlane) : ℝ := ρ.mix (fun i y => v i y + (w y - u i y)) x

 theorem circleMix_eq_adjusted
    (f : EuclideanPlane → UnitAddCircle) (u v : ι → EuclideanPlane → ℝ)
    (w : EuclideanPlane → ℝ) {x : EuclideanPlane} (hx : x ∈ Ω)
    (hw : (w x : UnitAddCircle) = f x) :
    ρ.circleMix f u v x = (ρ.adjustedCircleMix u v w x : UnitAddCircle) := by
  rw [circleMix, ← hw, ← AddCircle.coe_add]
  congr 1
  have hm := ρ.mix_add_scalar (fun i y => v i y - u i y) w hx
  have he : (fun i y => v i y + (w y - u i y)) = fun i y => (v i y - u i y) + w y := by
    funext i y
    ring
  rw [adjustedCircleMix, he, hm, add_comm]

 theorem adjustedCircleMix_mem_interval
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
    {x : EuclideanPlane} (hx : x ∈ Ω) {a b : ℝ}
    (hpatch : ∀ i, ρ.weight i x ≠ 0 → W i ⊆ V)
    (hbound : ∀ i, ρ.weight i x ≠ 0 → ∀ y ∈ W i, w y ∈ Icc a b) :
    ρ.adjustedCircleMix u v w x ∈ Icc a b := by
  apply ρ.mix_mem_Icc _ hx
  intro i hi
  have hxi := hsub i (subset_tsupport (ρ.weight i) hi)
  let c := w x - u i x
  have hc (y : EuclideanPlane) (hy : y ∈ W i) : w y - u i y = c :=
    circle_lift_difference_eq_on_preconnected (hW i) (hconn i)
      (hw.mono (hpatch i hi)) (hu i)
      (fun z hz => (hwlift z (hpatch i hi hz)).trans (hlift i z hz).symm) hy hxi
  have huB : ∀ y ∈ W i, u i y ∈ Icc (a - c) (b - c) := by
    intro y hy
    have hb := hbound i hi y hy
    have he := hc y hy
    constructor <;> linarith [hb.1, hb.2]
  have hvB := hav i (a - c) (b - c) huB x (subset_tsupport (ρ.weight i) hi)
  change v i x + (w x - u i x) ∈ Icc a b
  change v i x + c ∈ Icc a b
  constructor <;> linarith [hvB.1, hvB.2]

 theorem adjustedCircleMix_eventual_interval
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
    {s : EuclideanPlane} (hV : V ∈ 𝓝 s)
    (hpatch : LocalPatchSupport (Ω : Set EuclideanPlane) ρ.weight W s)
    {a b : ℝ} (hbound : ∀ᶠ y in 𝓝[(Ω : Set EuclideanPlane)] s, w y ∈ Icc a b) :
    ∀ᶠ x in 𝓝[(Ω : Set EuclideanPlane)] s, ρ.adjustedCircleMix u v w x ∈ Icc a b := by
  obtain ⟨T, hT, hTB⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hbound
  filter_upwards [self_mem_nhdsWithin, hpatch (T ∩ V) (inter_mem hT hV)] with x hx hp
  apply ρ.adjustedCircleMix_mem_interval W hW hconn hsub f u v hu hlift hav w hw hwlift hx
  · intro i hi y hy
    exact (hp i hi hy).2.2
  · intro i hi y hy
    have hh := hp i hi hy
    exact hTB ⟨hh.2.1, hh.1⟩

end OpenPlanePartition
end CircleDomainRigidity

end

end OAI
