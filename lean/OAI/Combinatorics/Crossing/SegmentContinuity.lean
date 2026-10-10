import OAI.Combinatorics.Crossing.SegmentParameters
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Tactic.FunProp

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Topology Classical

def ClosedSegmentsMeet (a b c d : Plane) : Prop :=
  ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ u ∈ Set.Icc (0 : ℝ) 1,
    segmentPoint a b t = segmentPoint c d u

theorem closedSegmentsMeet_of_proper (a b c d : Plane) (h : SegmentsCrossProperly a b c d) :
    ClosedSegmentsMeet a b c d := by
  obtain ⟨_,t,ht,u,hu,he⟩ := h
  exact ⟨t,⟨ht.1.le,ht.2.le⟩,u,⟨hu.1.le,hu.2.le⟩,he⟩

theorem isClosed_closedSegmentsMeet (c d : Plane) :
    IsClosed {ab : Plane × Plane | ClosedSegmentsMeet ab.1 ab.2 c d} := by
  let P := (Plane × Plane) × (unitInterval × unitInterval)
  let S : Set P := {x | segmentPoint x.1.1 x.1.2 x.2.1.val = segmentPoint c d x.2.2.val}
  have hS : IsClosed S := by
    apply isClosed_eq
    · dsimp [segmentPoint]
      fun_prop
    · dsimp [segmentPoint]
      fun_prop
  have hproj := (isClosedMap_fst_of_compactSpace : IsClosedMap (Prod.fst : P → Plane × Plane)) S hS
  have heq : Prod.fst '' S = {ab : Plane × Plane | ClosedSegmentsMeet ab.1 ab.2 c d} := by
    ext ab
    constructor
    · rintro ⟨⟨ab',t,u⟩,hx,h⟩
      change ab'=ab at h
      subst ab'
      exact ⟨t.val,t.property,u.val,u.property,hx⟩
    · rintro ⟨t,ht,u,hu,h⟩
      exact ⟨(ab,(⟨t,ht⟩,⟨u,hu⟩)),h,rfl⟩
  rwa [heq] at hproj

theorem eventually_segmentCrossingSign_of_proper (a b c d : Plane)
    (h : SegmentsCrossProperly a b c d) :
    ∀ᶠ ab : Plane × Plane in 𝓝 (a,b),
      segmentCrossingSign ab.1 ab.2 c d = segmentCrossingSign a b c d := by
  have hD : Continuous (fun ab : Plane × Plane => det2 (ab.2-ab.1) (d-c)) := by
    dsimp [det2]
    fun_prop
  have hF : ContinuousAt (fun ab : Plane × Plane => firstIntersectionParameter ab.1 ab.2 c d) (a,b) := by
    apply ContinuousAt.div
    · dsimp [det2]
      fun_prop
    · exact hD.continuousAt
    · exact h.1
  have hS : ContinuousAt (fun ab : Plane × Plane => secondIntersectionParameter ab.1 ab.2 c d) (a,b) := by
    apply ContinuousAt.div
    · dsimp [det2]
      fun_prop
    · exact hD.continuousAt
    · exact h.1
  obtain ⟨ht,hu⟩ := (segmentsCrossProperly_iff_parameters a b c d h.1).mp h
  have ht' := hF.eventually (isOpen_Ioo.mem_nhds ht)
  have hu' := hS.eventually (isOpen_Ioo.mem_nhds hu)
  by_cases hpos : 0 < det2 (b-a) (d-c)
  · have hd' : ∀ᶠ ab : Plane × Plane in 𝓝 (a,b), 0 < det2 (ab.2-ab.1) (d-c) :=
      continuousAt_const.eventually_lt hD.continuousAt hpos
    filter_upwards [ht',hu',hd'] with ab ht hu hd
    have hc := (segmentsCrossProperly_iff_parameters ab.1 ab.2 c d (ne_of_gt hd)).mpr ⟨ht,hu⟩
    simp [segmentCrossingSign,h,hc,hpos,hd]
  · have hneg : det2 (b-a) (d-c) < 0 := lt_of_le_of_ne (le_of_not_gt hpos) h.1
    have hd' : ∀ᶠ ab : Plane × Plane in 𝓝 (a,b), det2 (ab.2-ab.1) (d-c) < 0 :=
      hD.continuousAt.eventually_lt continuousAt_const hneg
    filter_upwards [ht',hu',hd'] with ab ht hu hd
    have hc := (segmentsCrossProperly_iff_parameters ab.1 ab.2 c d (ne_of_lt hd)).mpr ⟨ht,hu⟩
    simp [segmentCrossingSign,h,hc,hpos,not_lt.mpr hd.le]

def SegmentPairTransverse (a b c d : Plane) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u ∈ Set.Icc (0 : ℝ) 1,
    segmentPoint a b t = segmentPoint c d u →
      det2 (b-a) (d-c) ≠ 0 ∧ t ∈ Set.Ioo (0 : ℝ) 1 ∧ u ∈ Set.Ioo (0 : ℝ) 1

theorem eventually_segmentCrossingSign (a b c d : Plane) (h : SegmentPairTransverse a b c d) :
    ∀ᶠ ab : Plane × Plane in 𝓝 (a,b),
      segmentCrossingSign ab.1 ab.2 c d = segmentCrossingSign a b c d := by
  by_cases hc : SegmentsCrossProperly a b c d
  · exact eventually_segmentCrossingSign_of_proper a b c d hc
  · have hn : ¬ ClosedSegmentsMeet a b c d := by
      rintro ⟨t,ht,u,hu,he⟩
      obtain ⟨hd,ht',hu'⟩ := h t ht u hu he
      exact hc ⟨hd,t,ht',u,hu',he⟩
    have hevent := (isClosed_closedSegmentsMeet c d).isOpen_compl.mem_nhds
      (show (a,b) ∈ {ab : Plane × Plane | ClosedSegmentsMeet ab.1 ab.2 c d}ᶜ from hn)
    filter_upwards [hevent] with ab hab
    have hn' : ¬ SegmentsCrossProperly ab.1 ab.2 c d :=
      fun hx => hab (closedSegmentsMeet_of_proper _ _ _ _ hx)
    simp [segmentCrossingSign,hc,hn']

end Zarankiewicz

end

end OAI
