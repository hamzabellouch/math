import OAI.Combinatorics.CompleteCrossing.Plane
import OAI.Combinatorics.Crossing.LocalSegmentTransversality
import OAI.Combinatorics.Crossing.ProperCrossingLocality
import OAI.Combinatorics.Crossing.SegmentAffineForms
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Topology.Separation.Hausdorff

namespace OAI

/-! Local straightness and transversality of normalized drawings. -/

section

/-! Actual local line and adjacency properties used in the cycle-intersection proof. -/
noncomputable section
open Zarankiewicz
namespace Paper170Geometry
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

structure NoAdjacentCrossings (D : Paper170.AdmissibleDrawing graph) : Prop where
  eq_empty : ∀ e f : Edge, e≠f →
    (graph.src e=graph.src f ∨ graph.src e=graph.dst f ∨
      graph.dst e=graph.src f ∨ graph.dst e=graph.dst f) →
    Paper170.edgeInterior D.toContinuousDrawing e ∩
      Paper170.edgeInterior D.toContinuousDrawing f = ∅

structure LocallyStraightAt (D : Paper170.ContinuousDrawing graph) (e : Edge) (x : Plane) : Prop where
  exists_line : ∃a b : Plane, a≠b ∧ x∈openSegmentTrace a b ∧
    ∃U : Set Plane, IsOpen U ∧ x∈U ∧
      ∀z∈U, z∈Paper170.edgeInterior D e ↔ z∈openSegmentTrace a b

structure LocallyStraightCrossings (D : Paper170.AdmissibleDrawing graph) : Prop where
  at_crossing : ∀e f : Edge, e≠f → ∀x,
    x∈Paper170.edgeInterior D.toContinuousDrawing e →
    x∈Paper170.edgeInterior D.toContinuousDrawing f →
      LocallyStraightAt D.toContinuousDrawing e x ∧ LocallyStraightAt D.toContinuousDrawing f x

structure LocallyTransverseCrossings (D : Paper170.AdmissibleDrawing graph) : Prop where
  at_crossing : ∀e f : Edge, e≠f → ∀x,
    x∈Paper170.edgeInterior D.toContinuousDrawing e →
    x∈Paper170.edgeInterior D.toContinuousDrawing f →
      ∃a b c d : Plane, det2 (b-a) (d-c)≠0 ∧
        x∈openSegmentTrace a b ∧ x∈openSegmentTrace c d ∧
        ∃U : Set Plane, IsOpen U ∧ x∈U ∧
          (∀z∈U, z∈Paper170.edgeInterior D.toContinuousDrawing e ↔ z∈openSegmentTrace a b) ∧
          (∀z∈U, z∈Paper170.edgeInterior D.toContinuousDrawing f ↔ z∈openSegmentTrace c d)

theorem normalized_noAdjacent (N : Paper170.NormalizedDrawing graph) :
    NoAdjacentCrossings N.toAdmissibleDrawing :=
  ⟨fun e f hef hadj => Set.disjoint_iff_inter_eq_empty.mp (N.no_adjacent e f hef hadj)⟩

end Paper170Geometry

end
end

section

noncomputable section
open Set Zarankiewicz
namespace Paper170Geometry

/-- A point away from the subdivision knots lies strictly inside one piece. -/
theorem parametrization_knot_interval {a b : Paper170.Plane} {γ : Path a b}
    (P : Paper170.PolygonalParametrization γ) (t : unitInterval)
    (ht : t ∈ Ioo (0 : unitInterval) 1) (hne : ∀i, t ≠ P.knot i) :
    ∃i : Fin P.pieces, P.knot i.castSucc < t ∧ t < P.knot i.succ := by
  classical
  have hex : ∃i, t < P.knot i := ⟨Fin.last P.pieces, by simpa only [P.last] using ht.2⟩
  let j := Fin.find (fun i => t < P.knot i) hex
  have hj : t < P.knot j := Fin.find_spec hex
  have hj0 : j ≠ 0 := by
    intro he
    rw [he, P.first] at hj
    exact (lt_asymm ht.1 hj)
  obtain ⟨i, hi⟩ := Fin.exists_succ_eq_of_ne_zero hj0
  refine ⟨i, ?_, by simpa only [hi] using hj⟩
  have hm : ¬t < P.knot i.castSucc := Fin.find_min hex (by change i.castSucc < j; rw [← hi]; exact Fin.castSucc_lt_succ)
  exact lt_of_le_of_ne (le_of_not_gt hm) (hne i.castSucc).symm

/-- The open part of a subdivided path is exactly its open segment. -/
theorem parametrization_open_piece {a b : Paper170.Plane} {γ : Path a b}
    (P : Paper170.PolygonalParametrization γ) (i : Fin P.pieces) :
    γ '' Ioo (P.knot i.castSucc) (P.knot i.succ) =
      openSegmentTrace (P.vertices i.val) (P.vertices (i.val+1)) := by
  have hab := P.increasing (Fin.castSucc_lt_succ (i := i))
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨u, hu⟩ := intervalSegment_surjective_interval _ _ hab t ⟨ht.1.le, ht.2.le⟩
    have hu0 : 0 < (u : ℝ) := by
      by_contra hn
      have hue : u = 0 := Subtype.ext (le_antisymm (le_of_not_gt hn) u.property.1)
      have he : P.knot i.castSucc = t := by simpa [hue, intervalSegment] using hu
      exact ht.1.ne he
    have hu1 : (u : ℝ) < 1 := by
      by_contra hn
      have hue : u = 1 := Subtype.ext (le_antisymm u.property.2 (le_of_not_gt hn))
      have he : P.knot i.succ = t := by simpa [hue, intervalSegment] using hu
      exact ht.2.ne he.symm
    refine ⟨u, ⟨hu0, hu1⟩, ?_⟩
    exact ((Paper170.toZarankiewiczParametrization P).segment_formula i u).symm.trans
      (congrArg γ hu)
  · rintro ⟨s, hs, rfl⟩
    let u : unitInterval := ⟨s, hs.1.le, hs.2.le⟩
    refine ⟨intervalSegment (P.knot i.castSucc) (P.knot i.succ) u,
      intervalSegment_strict_between _ _ u hab hs, ?_⟩
    exact (Paper170.toZarankiewiczParametrization P).segment_formula i u

/-- An injective polygonal path is locally a straight segment away from its knots. -/
theorem locallyStraightAt_of_not_knot {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
    (D : Paper170.ContinuousDrawing graph) (e : Edge)
    (P : Paper170.PolygonalParametrization (D.edge e)) (t : unitInterval)
    (ht : t ∈ Ioo (0 : unitInterval) 1) (hne : ∀i, t ≠ P.knot i) :
    LocallyStraightAt D e (D.edge e t) := by
  obtain ⟨i, hti⟩ := parametrization_knot_interval P t ht hne
  have hem := (D.edge e).continuous.isClosedEmbedding (D.edge_injective e)
  obtain ⟨U, hU, heq⟩ := hem.isInducing.isOpen_iff.mp
    (isOpen_Ioo : IsOpen (Ioo (P.knot i.castSucc) (P.knot i.succ)))
  have hpiece := parametrization_open_piece P i
  have hsub : Ioo (P.knot i.castSucc) (P.knot i.succ) ⊆ Ioo (0 : unitInterval) 1 := by
    intro s hs
    exact ⟨lt_of_le_of_lt (P.knot i.castSucc).property.1 hs.1,
      lt_of_lt_of_le hs.2 (P.knot i.succ).property.2⟩
  refine ⟨P.vertices i.val, P.vertices (i.val+1), ?_, ?_, U, hU, ?_, ?_⟩
  · exact fun he => P.direction_ne_zero (D.edge_injective e) i.val i.isLt (sub_eq_zero.mpr he.symm)
  · rw [← hpiece]
    exact ⟨t, hti, rfl⟩
  · change t ∈ (D.edge e) ⁻¹' U
    rw [heq]
    exact hti
  · intro z hz
    rw [← hpiece]
    constructor
    · rintro ⟨s, _, rfl⟩
      refine ⟨s, ?_, rfl⟩
      rw [← heq]
      exact hz
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hsub hs, rfl⟩

theorem normalized_locallyStraight {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
    (N : Paper170.NormalizedDrawing graph) : LocallyStraightCrossings N.toAdmissibleDrawing := by
  refine ⟨?_⟩
  intro e f hef x hxe hxf
  have hx : x ∈ Paper170.crossingPoints N.toContinuousDrawing := ⟨e, f, hef, hxe, hxf⟩
  have hlocal (g : Edge) (hg : x ∈ Paper170.edgeInterior N.toContinuousDrawing g) :
      LocallyStraightAt N.toContinuousDrawing g x := by
    obtain ⟨t, ht, rfl⟩ := hg
    apply locallyStraightAt_of_not_knot N.toContinuousDrawing g (N.polygonal g) t ht
    intro i he
    exact N.crossings_not_knots g i (he ▸ hx)
  exact ⟨hlocal e hxe, hlocal f hxf⟩

end Paper170Geometry

end
end

section

noncomputable section
open Set Zarankiewicz
open scoped Topology
namespace Paper170Geometry

/-- A crossing chart makes the local intersection a single point. -/
theorem properCrossing_locally_unique (A B : Set Paper170.Plane) (x : Paper170.Plane)
    (h : Paper170.ProperCrossing A B x) :
    ∃U : Set Paper170.Plane, IsOpen U ∧ x ∈ U ∧
      ∀y ∈ U, y ∈ A → y ∈ B → y = x := by
  obtain ⟨chart, hx, hz, hA, hB⟩ := h.chart_exists
  refine ⟨chart.source, chart.open_source, hx, ?_⟩
  intro y hy hyA hyB
  have hyA' := (chart_image_mem_iff chart A {z | z.2=0} hA y hy).mp hyA
  have hyB' := (chart_image_mem_iff chart B {z | z.1=0} hB y hy).mp hyB
  apply chart.injOn hy hx
  rw [hz]
  exact Prod.ext hyB' hyA'

/-- Two straight segments meeting locally only once have independent directions. -/
theorem local_segment_directions_ne_zero (a b c d x : Plane)
    (hab : a ≠ b) (hcd : c ≠ d)
    (hxab : x ∈ openSegmentTrace a b) (hxcd : x ∈ openSegmentTrace c d)
    (U : Set Plane) (hU : IsOpen U) (hxU : x ∈ U)
    (hunique : ∀y ∈ U, y ∈ openSegmentTrace a b → y ∈ openSegmentTrace c d → y=x) :
    det2 (b-a) (d-c) ≠ 0 := by
  intro hdet
  obtain ⟨s, hs, hsx⟩ := hxab
  obtain ⟨t, ht, htx⟩ := hxcd
  let k := dot2 (b-a) (d-c) / squaredLength (b-a)
  have hparallel : d-c = k • (b-a) := vector_parallel_of_det_zero _ _ (sub_ne_zero.mpr hab.symm) hdet
  let f : ℝ → Plane := fun r => x + r • (d-c)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hf0 : f 0 = x := by simp [f]
  have hevent : ∀ᶠr : ℝ in 𝓝 0,
      f r ∈ U ∧ s+r*k ∈ Ioo (0:ℝ) 1 ∧ t+r ∈ Ioo (0:ℝ) 1 := by
    have h₁ := hf.continuousAt.eventually (show U ∈ 𝓝 (f 0) by simpa only [hf0] using hU.mem_nhds hxU)
    have h₂ : ∀ᶠr : ℝ in 𝓝 0, s+r*k ∈ Ioo (0:ℝ) 1 := by
      have hc : Continuous (fun r : ℝ => s+r*k) := by fun_prop
      apply hc.continuousAt.eventually
      change Ioo (0:ℝ) 1 ∈ 𝓝 (s+0*k)
      simpa only [zero_mul, add_zero] using (isOpen_Ioo.mem_nhds hs)
    have h₃ : ∀ᶠr : ℝ in 𝓝 0, t+r ∈ Ioo (0:ℝ) 1 := by
      have hc : Continuous (fun r : ℝ => t+r) := by fun_prop
      apply hc.continuousAt.eventually
      change Ioo (0:ℝ) 1 ∈ 𝓝 (t+0)
      simpa only [add_zero] using (isOpen_Ioo.mem_nhds ht)
    filter_upwards [h₁, h₂, h₃] with r h₁ h₂ h₃ using ⟨h₁,h₂,h₃⟩
  obtain ⟨ε, hε, hsmall⟩ := Metric.eventually_nhds_iff.mp hevent
  have he : dist (ε/2) (0:ℝ) < ε := by rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith
  obtain ⟨hfU, hs', ht'⟩ := hsmall he
  have habf : segmentPoint a b (s+(ε/2)*k) = f (ε/2) := by
    dsimp [f]
    rw [segmentPoint_start_form, show x = a+s • (b-a) from hsx.symm.trans (segmentPoint_start_form a b s)]
    rw [hparallel, smul_smul, add_smul]
    abel
  have hcdf : segmentPoint c d (t+ε/2) = f (ε/2) := by
    dsimp [f]
    rw [segmentPoint_start_form, show x = c+t • (d-c) from htx.symm.trans (segmentPoint_start_form c d t)]
    rw [add_smul]
    abel
  have hfx : f (ε/2) = x := hunique _ hfU ⟨_,hs',habf⟩ ⟨_,ht',hcdf⟩
  have hzero : (ε/2) • (d-c) = 0 := by simpa only [f, add_eq_left] using hfx
  exact (smul_eq_zero.mp hzero).elim (ne_of_gt (by positivity)) (sub_ne_zero.mpr hcd.symm)

/-- Local straightness and the actual crossing charts imply transversality. -/
theorem locallyTransverse_of_locallyStraight {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
    (D : Paper170.AdmissibleDrawing graph) (h : LocallyStraightCrossings D) :
    LocallyTransverseCrossings D := by
  refine ⟨?_⟩
  intro e f hef x hxe hxf
  obtain ⟨he,hf⟩ := h.at_crossing e f hef x hxe hxf
  obtain ⟨a,b,hab,hxab,U,hU,hxU,hAU⟩ := he.exists_line
  obtain ⟨c,d,hcd,hxcd,V,hV,hxV,hBV⟩ := hf.exists_line
  obtain ⟨W,hW,hxW,hunique⟩ := properCrossing_locally_unique _ _ x (D.crossings_proper e f hef x hxe hxf)
  have hdet : det2 (b-a) (d-c) ≠ 0 := by
    apply local_segment_directions_ne_zero a b c d x hab hcd hxab hxcd (U∩V∩W)
      ((hU.inter hV).inter hW) ⟨⟨hxU,hxV⟩,hxW⟩
    intro y hy hyA hyB
    exact hunique y hy.2 ((hAU y hy.1.1).mpr hyA) ((hBV y hy.1.2).mpr hyB)
  exact ⟨a,b,c,d,hdet,hxab,hxcd,U∩V,hU.inter hV,⟨hxU,hxV⟩,
    fun y hy => hAU y hy.1,fun y hy => hBV y hy.2⟩

theorem normalized_locallyTransverse {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
    (N : Paper170.NormalizedDrawing graph) : LocallyTransverseCrossings N.toAdmissibleDrawing :=
  locallyTransverse_of_locallyStraight N.toAdmissibleDrawing (normalized_locallyStraight N)

end Paper170Geometry

end
end

end OAI
