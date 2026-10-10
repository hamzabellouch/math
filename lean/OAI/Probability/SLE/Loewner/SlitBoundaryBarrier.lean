import OAI.Probability.SLE.Loewner.InitialCapacity
import OAI.Probability.SLE.Loewner.TraceBoundaryBarrier

namespace OAI

/-! Compact, locally path-connected boundary barriers for static attached slits. -/
noncomputable section
open Set Filter Metric Function
open scoped Topology

namespace SLEExactGauge

def slitBoundaryBarrier (p : C(unitInterval,ℂ)) (R : ℝ) : Set ℂ :=
  range p ∪ (Complex.ofReal '' Icc (-R) R)

lemma slitBoundaryBarrier_compact (p : C(unitInterval,ℂ)) (R : ℝ) :
    IsCompact (slitBoundaryBarrier p R) :=
  (isCompact_range p.continuous).union (isCompact_Icc.image Complex.continuous_ofReal)

lemma slitBoundaryBarrier_locallyPathConnected (p : C(unitInterval,ℂ))
    (R : ℝ) (hR : 0≤R) : LocallyPathConnectedSpace (slitBoundaryBarrier p R) := by
  have : LocallyPathConnectedSpace unitInterval :=
    (isQuotientMap_projIcc (a := (0:ℝ)) (b := 1) (h := zero_le_one)).locallyPathConnectedSpace
  let q : unitInterval → range p := fun t => ⟨p t,mem_range_self t⟩
  have hq : Continuous q := p.continuous.subtype_mk _
  have hs : Surjective q := by
    rintro ⟨_,t,rfl⟩
    exact ⟨t,rfl⟩
  have : LocallyPathConnectedSpace (range p) :=
    (hq.isClosedMap.isQuotientMap hq hs).locallyPathConnectedSpace
  have : LocallyPathConnectedSpace (Icc (-R) R) :=
    (isQuotientMap_projIcc (a := -R) (b := R) (h := by linarith)).locallyPathConnectedSpace
  let r : Icc (-R) R → Complex.ofReal '' Icc (-R) R := fun x => ⟨x,⟨x,x.2,rfl⟩⟩
  have hr : Continuous r := (Complex.continuous_ofReal.comp continuous_subtype_val).subtype_mk _
  have hs : Surjective r := by
    rintro ⟨_,x,hx,rfl⟩
    exact ⟨⟨x,hx⟩,rfl⟩
  have : LocallyPathConnectedSpace (Complex.ofReal '' Icc (-R) R) :=
    (hr.isClosedMap.isQuotientMap hr hs).locallyPathConnectedSpace
  exact compact_union_locallyPathConnected (isCompact_range p.continuous)
    (isCompact_Icc.image Complex.continuous_ofReal)

lemma slitBoundaryBarrier_disjoint_domain (p : C(unitInterval,ℂ)) (R : ℝ) :
    Disjoint (slitBoundaryBarrier p R) (upperHalfPlane \ range p) := by
  apply disjoint_left.mpr
  intro z hz hD
  rcases hz with hz | ⟨x,_,rfl⟩
  · exact hD.2 hz
  · have him := hD.1
    change 0<(x:ℂ).im at him
    simp at him

lemma frontier_mem_slitBoundaryBarrier (p : C(unitInterval,ℂ)) {R : ℝ} {z : ℂ}
    (hz : z∈frontier (upperHalfPlane \ range p)) (hR : ‖z‖≤R) :
    z∈slitBoundaryBarrier p R := by
  by_cases hp : z∈range p
  · exact Or.inl hp
  right
  have hsub : upperHalfPlane \ range p ⊆ {w : ℂ | 0≤w.im} := by
    intro w hw
    exact (show 0<w.im from hw.1).le
  have hznonneg : 0≤z.im :=
    (closure_minimal hsub
      (isClosed_le continuous_const Complex.continuous_im)) hz.1
  have ho : IsOpen (upperHalfPlane \ range p) :=
    isOpen_upperHalfPlane.sdiff (isCompact_range p.continuous).isClosed
  have hznot : z∉upperHalfPlane \ range p := by simpa only [ho.interior_eq] using hz.2
  have him : z.im=0 := by
    by_contra he
    exact hznot ⟨lt_of_le_of_ne hznonneg (Ne.symm he),hp⟩
  refine ⟨z.re,?_,?_⟩
  · have hh := (Complex.abs_re_le_norm z).trans hR
    exact ⟨by linarith [(neg_abs_le z.re)],(le_abs_self z.re).trans hh⟩
  · apply Complex.ext <;> simp [him]

lemma slitBoundaryBarrier_uniform_paths (p : C(unitInterval,ℂ))
    (R : ℝ) (hR : 0≤R) (ε : ℝ) (hε : 0<ε) :
    ∃ δ : ℝ, 0<δ ∧ ∀ x∈slitBoundaryBarrier p R, ∀ y∈slitBoundaryBarrier p R,
      dist x y<δ → ∃ q : Path x y, (∀ s, q s∈slitBoundaryBarrier p R) ∧
        ∀ s, dist (q s) x<ε := by
  have : CompactSpace (slitBoundaryBarrier p R) :=
    isCompact_iff_compactSpace.mp (slitBoundaryBarrier_compact p R)
  have : LocallyPathConnectedSpace (slitBoundaryBarrier p R) :=
    slitBoundaryBarrier_locallyPathConnected p R hR
  obtain ⟨δ,hδ,hpath⟩ := compact_locallyPathConnected_uniform_path
    (A := slitBoundaryBarrier p R) ε hε
  refine ⟨δ,hδ,fun x hx y hy hxy => ?_⟩
  obtain ⟨q,hq⟩ := hpath ⟨x,hx⟩ ⟨y,hy⟩ hxy
  exact ⟨q.map continuous_subtype_val,fun s => (q s).property,hq⟩

end SLEExactGauge

end

end OAI
