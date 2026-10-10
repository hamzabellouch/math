import Mathlib

namespace OAI

section
section
section
noncomputable section
section
section
section
section
open Set MeasureTheory
open scoped BigOperators
open Set Topology

namespace CannonContinuum

lemma clopen_neighborhood_of_component {X : Type*} [TopologicalSpace X]
    [T2Space X] [CompactSpace X] (x : X) {U : Set X} (hU : IsOpen U)
    (hC : connectedComponent x ⊆ U) :
    ∃ W : Set X, IsClopen W ∧ x ∈ W ∧ W ⊆ U := by
  let S := {s : Set X // IsClopen s ∧ x ∈ s}
  have hnull : Uᶜ ∩ ⋂ s : S, (s : Set X) = ∅ := by
    rw [← connectedComponent_eq_iInter_isClopen]
    exact disjoint_iff_inter_eq_empty.mp (disjoint_compl_left_iff_subset.mpr hC)
  obtain ⟨T, hT⟩ := hU.isClosed_compl.isCompact.elim_finite_subfamily_closed
    (fun s : S => (s : Set X)) (fun s => s.property.1.isClosed)
    (disjoint_iff_inter_eq_empty.mpr hnull)
  refine ⟨⋂ s ∈ T, (s : Set X), isClopen_biInter_finset (fun s _ => s.property.1),
    mem_iInter₂.mpr (fun s _ => s.property.2), ?_⟩
  exact disjoint_compl_left_iff_subset.mp hT

theorem component_meets_level {X : Type*} [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [PreconnectedSpace X]
    (f : X → ℝ) (hf : Continuous f) (r : ℝ)
    (x : {z : X // r ≤ f z}) (hbelow : ∃ y : X, f y < r) :
    ∃ z ∈ connectedComponent x, f (z : X) = r := by
  let K : Set X := {z | r ≤ f z}
  have hK : IsClosed K := isClosed_le continuous_const hf
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK.isCompact
  by_contra hn
  push Not at hn
  have hC : connectedComponent x ⊆ {z : K | r < f (z : X)} := by
    intro z hz
    exact lt_of_le_of_ne z.property (Ne.symm (hn z hz))
  obtain ⟨W, hW, hxW, hWU⟩ := clopen_neighborhood_of_component (X := K) x
    (isOpen_lt continuous_const (hf.comp continuous_subtype_val)) hC
  let V : Set X := Subtype.val '' W
  have hVc : IsClosed V := hK.isClosedMap_subtype_val W hW.isClosed
  have hVo : IsOpen V := by
    obtain ⟨O, hO, hOW⟩ := isOpen_induced_iff.mp hW.isOpen
    have hV : V = O ∩ {z | r < f z} := by
      ext z
      constructor
      · rintro ⟨z', hz', rfl⟩
        exact ⟨by simpa only [← hOW, mem_preimage] using hz', hWU hz'⟩
      · rintro ⟨hzO, hzr⟩
        refine ⟨⟨z, show r ≤ f z from hzr.le⟩, ?_, rfl⟩
        simpa only [← hOW, mem_preimage] using hzO
    rw [hV]
    exact hO.inter (isOpen_lt continuous_const hf)
  have hVall : V = univ := (show IsClopen V from ⟨hVc, hVo⟩).eq_univ ⟨x, x, hxW, rfl⟩
  obtain ⟨y, hy⟩ := hbelow
  have hyV : y ∈ V := by rw [hVall]; trivial
  obtain ⟨z, hz, hzy⟩ := hyV
  have := z.property
  rw [hzy] at this
  exact (not_lt_of_ge this) hy

theorem stop_continuum {X : Type*} [MetricSpace X]
    {D : Set X} (hD : IsCompact D) (hconn : IsConnected D)
    {p x : X} {r : ℝ} (hx : x ∈ D) (hxr : r < dist x p)
    (hin : ∃ y ∈ D, dist y p < r) :
    ∃ C : Set X, IsCompact C ∧ IsConnected C ∧ C ⊆ D ∧ x ∈ C ∧
      (∃ z ∈ C, dist z p = r) ∧ ∀ z ∈ C, r ≤ dist z p := by
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD
  let : PreconnectedSpace D := Subtype.preconnectedSpace hconn.isPreconnected
  let f : D → ℝ := fun z => dist (z : X) p
  have hf : Continuous f := continuous_subtype_val.dist continuous_const
  let K : Set D := {z | r ≤ f z}
  let xK : K := ⟨⟨x, hx⟩, hxr.le⟩
  have hK : IsClosed K := isClosed_le continuous_const hf
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK.isCompact
  have hbelow : ∃ y : D, f y < r := by
    obtain ⟨y, hyD, hyr⟩ := hin
    exact ⟨⟨y, hyD⟩, hyr⟩
  obtain ⟨z, hz, hzr⟩ := component_meets_level f hf r xK hbelow
  let g : K → X := fun z => z.val.val
  have hg : Continuous g := continuous_subtype_val.comp continuous_subtype_val
  refine ⟨g '' connectedComponent xK, isClosed_connectedComponent.isCompact.image hg,
    isConnected_connectedComponent.image g hg.continuousOn, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact y.val.property
  · exact ⟨xK, mem_connectedComponent, rfl⟩
  · exact ⟨g z, ⟨z, hz, rfl⟩, hzr⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact y.property

end CannonContinuum

end
end
end
end
end
end
end
end

end OAI
