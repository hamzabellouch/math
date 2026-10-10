import OAI.Geometry.SurfaceImmersion.Atlas.MatchedSubsetChart

namespace OAI

/-! Compact embedded arcs with open interior, used to reduce the
compact one-dimensional curve to finitely many interval pieces. -/
noncomputable section
open Set Filter Metric Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable (X : Type*) [TopologicalSpace X]

structure CompactCurveArc where
  left : ℝ
  right : ℝ
  ordered : left < right
  map : Icc left right → X
  embedding : IsClosedEmbedding map
  interior_open : IsOpen (map '' {t | left < (t:ℝ) ∧ (t:ℝ) < right})

variable {X} [T2Space X]

theorem line_chart_compact_arc_data (c : OpenPartialHomeomorph X ℝ) {p : X}
    (hp : p ∈ c.source) :
    ∃ (A : CompactCurveArc X) (V : Set X), IsOpen V ∧ p ∈ V ∧ V ⊆ range A.map ∧
      ∃ t : Icc A.left A.right, A.left < (t:ℝ) ∧ (t:ℝ) < A.right ∧ A.map t = p ∧
        V = A.map '' {u | A.left < (u:ℝ) ∧ (u:ℝ) < A.right} ∧ V ⊆ c.source := by
  obtain ⟨r,hr,hrt⟩ := nhds_basis_closedBall.mem_iff.mp (c.open_target.mem_nhds (c.map_source hp))
  let a := c p-r
  let b := c p+r
  have hab : a < b := by dsimp [a,b]; linarith
  have hinterval : Icc a b ⊆ c.target := by
    intro t ht
    apply hrt
    rw [mem_closedBall,Real.dist_eq,abs_le]
    constructor <;> dsimp [a,b] at ht <;> linarith [ht.1,ht.2]
  let γ : Icc a b → X := fun t => c.symm t
  have hγcont : Continuous γ := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (c.symm.continuousAt (hinterval t.property)).comp continuous_subtype_val.continuousAt
  have hγinj : Function.Injective γ := by
    intro s t hst
    exact Subtype.ext (c.symm.injOn (hinterval s.property) (hinterval t.property) hst)
  have heq : γ '' {t | a < (t:ℝ) ∧ (t:ℝ) < b} = c.symm '' Ioo a b := by
    ext z
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨t,ht,rfl⟩
    · rintro ⟨t,ht,rfl⟩
      exact ⟨⟨t,ht.1.le,ht.2.le⟩,ht,rfl⟩
  have hV : IsOpen (c.symm '' Ioo a b) :=
    c.isOpen_image_symm_of_subset_target isOpen_Ioo (fun _ ht => hinterval ⟨ht.1.le,ht.2.le⟩)
  let A : CompactCurveArc X := ⟨a,b,hab,γ,hγcont.isClosedEmbedding hγinj,by rw [heq]; exact hV⟩
  refine ⟨A,c.symm '' Ioo a b,hV,?_,?_,?_⟩
  · refine ⟨c p,?_,c.left_inv hp⟩
    constructor <;> dsimp [a,b] <;> linarith
  · rintro z ⟨t,ht,rfl⟩
    exact ⟨⟨t,ht.1.le,ht.2.le⟩,rfl⟩

  · have ht : a < c p ∧ c p < b := by constructor <;> dsimp [a,b] <;> linarith
    refine ⟨⟨c p,ht.1.le,ht.2.le⟩,ht.1,ht.2,c.left_inv hp,heq.symm,?_⟩
    rintro z ⟨u,hu,rfl⟩
    exact c.map_target (hinterval ⟨hu.1.le,hu.2.le⟩)

theorem line_chart_compact_arc (c : OpenPartialHomeomorph X ℝ) {p : X}
    (hp : p ∈ c.source) :
    ∃ (A : CompactCurveArc X) (V : Set X), IsOpen V ∧ p ∈ V ∧ V ⊆ range A.map := by
  obtain ⟨A,V,hV,hpV,hAV,_⟩ := line_chart_compact_arc_data c hp
  exact ⟨A,V,hV,hpV,hAV⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
