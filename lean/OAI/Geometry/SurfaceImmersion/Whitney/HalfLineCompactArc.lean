import OAI.Geometry.SurfaceImmersion.Geometry.EmbeddedOpenSubset

namespace OAI

/-! Compact arcs at a half-line chart, including the boundary point in
an open neighborhood of the ambient curve. -/
noncomputable section
open Set Filter Metric Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X] [T2Space X]

theorem half_line_compact_arc_data (c : OpenPartialHomeomorph X (Ici (0:ℝ))) {p : X}
    (hp : p ∈ c.source) (hzero : c p = ⟨0,by simp⟩) :
    ∃ (A : CompactCurveArc X) (V : Set X), IsOpen V ∧ p ∈ V ∧ V ⊆ range A.map ∧
      A.map ⟨A.left,le_rfl,A.ordered.le⟩ = p ∧
      V \ {p} = A.openSubarc A.left A.right ∧ V ⊆ c.source := by
  let z : Ici (0:ℝ) := ⟨0,by simp⟩
  have hcz : c p = z := hzero
  have hz : z ∈ c.target := by rw [← hcz]; exact c.map_source hp
  obtain ⟨r,hr,hrt⟩ := nhds_basis_closedBall.mem_iff.mp (c.open_target.mem_nhds hz)
  have hT (t : Ici (0:ℝ)) (ht : (t:ℝ) ≤ r) : t ∈ c.target := by
    apply hrt
    change dist (t:ℝ) (0:ℝ) ≤ r
    have ht0 : 0 ≤ (t:ℝ) := t.property
    simpa only [Real.dist_eq,sub_zero,abs_of_nonneg ht0] using ht
  let j : Icc (0:ℝ) r → Ici (0:ℝ) := fun t => ⟨t.val,t.property.1⟩
  have hj : Continuous j := continuous_subtype_val.subtype_mk _
  let γ : Icc (0:ℝ) r → X := fun t => c.symm (j t)
  have hγcont : Continuous γ := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (c.symm.continuousAt (hT (j t) t.property.2)).comp hj.continuousAt
  have hγinj : Function.Injective γ := by
    intro s t hst
    have he := c.symm.injOn (hT (j s) s.property.2) (hT (j t) t.property.2) hst
    exact Subtype.ext (congrArg (fun u : Ici (0:ℝ) => (u:ℝ)) he)
  let O : Set (Ici (0:ℝ)) := {t | 0 < (t:ℝ) ∧ (t:ℝ) < r}
  have hO : IsOpen O := isOpen_Ioo.preimage continuous_subtype_val
  have hOT : O ⊆ c.target := fun t ht => hT t ht.2.le
  have heq : γ '' {t | 0 < (t:ℝ) ∧ (t:ℝ) < r} = c.symm '' O := by
    ext x
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨j t,ht,rfl⟩
    · rintro ⟨t,ht,rfl⟩
      exact ⟨⟨t.val,ht.1.le,ht.2.le⟩,ht,rfl⟩
  let A : CompactCurveArc X := ⟨0,r,hr,γ,hγcont.isClosedEmbedding hγinj,
    by rw [heq]; exact c.isOpen_image_symm_of_subset_target hO hOT⟩
  let W : Set (Ici (0:ℝ)) := {t | (t:ℝ) < r}
  have hW : IsOpen W := isOpen_Iio.preimage continuous_subtype_val
  have hWT : W ⊆ c.target := fun t ht => hT t ht.le
  refine ⟨A,c.symm '' W,c.isOpen_image_symm_of_subset_target hW hWT,?_,?_,?_,?_,?_⟩
  · refine ⟨z,hr,?_⟩
    rw [← hcz,c.left_inv hp]
  · rintro x ⟨t,ht,rfl⟩
    exact ⟨⟨t.val,t.property,ht.le⟩,rfl⟩

  · change c.symm (j ⟨0,le_rfl,hr.le⟩) = p
    change c.symm z = p
    rw [← hcz,c.left_inv hp]
  · apply Subset.antisymm
    · rintro x ⟨⟨t,ht,rfl⟩,hne⟩
      have htpos : 0 < (t:ℝ) := by
        have ht0 : 0 ≤ (t:ℝ) := t.property
        apply lt_of_le_of_ne ht0
        intro he
        have htz : t = z := Subtype.ext he.symm
        apply hne
        change c.symm t = p
        rw [htz,← hcz,c.left_inv hp]
      exact ⟨⟨t.val,t.property,ht.le⟩,⟨htpos,ht⟩,rfl⟩
    · rintro x ⟨t,ht,rfl⟩
      refine ⟨⟨j t,ht.2,rfl⟩,?_⟩
      intro he
      change c.symm (j t) = p at he
      have heq : j t = z := c.symm.injOn (hT (j t) t.property.2) hz (by
        rw [he,← hcz,c.left_inv hp])
      have hv := congrArg (fun s : Ici (0:ℝ) => (s:ℝ)) heq
      have ht0 : (t:ℝ) = 0 := hv
      exact (ne_of_gt ht.1) ht0
  · rintro x ⟨t,ht,rfl⟩
    exact c.map_target (hWT ht)

theorem half_line_compact_arc (c : OpenPartialHomeomorph X (Ici (0:ℝ))) {p : X}
    (hp : p ∈ c.source) (hzero : c p = ⟨0,by simp⟩) :
    ∃ (A : CompactCurveArc X) (V : Set X), IsOpen V ∧ p ∈ V ∧ V ⊆ range A.map := by
  obtain ⟨A,V,hV,hpV,hAV,_,_,_⟩ := half_line_compact_arc_data c hp hzero
  exact ⟨A,V,hV,hpV,hAV⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
