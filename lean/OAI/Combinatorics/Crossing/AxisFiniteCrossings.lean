import OAI.Combinatorics.Crossing.AxisContinuousDrawing
import Mathlib.Data.Set.Finite.Lattice

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

theorem axis_open_intersection_subsingleton (a b c d : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hne : (a,b) ≠ (c,d)) :
    (openSegmentTrace (0,a) (b,0) ∩ openSegmentTrace (0,c) (d,0)).Subsingleton := by
  rintro x ⟨⟨t,ht,he⟩,⟨u,hu,hf⟩⟩ y ⟨⟨t',ht',he'⟩,⟨u',hu',hf'⟩⟩
  have hmeet : axisSegmentPoint a b t=axisSegmentPoint c d u := he.trans hf.symm
  have hdet := axisSegmentPoint_meeting_det a b c d t u ha hb hne hmeet
  have hh := segment_intersection_parameters_unique (0,a) (b,0) (0,c) (d,0) hdet t u t' u'
    (he.trans hf.symm) (he'.trans hf'.symm)
  exact he.symm.trans ((congrArg (segmentPoint (0,a) (b,0)) hh.1).trans he')

theorem axis_intercept_pair_ne (a : Fin m → ℝ) (b : Fin n → ℝ)
    (hai : Function.Injective a) (hbi : Function.Injective b) (e f : BipartiteEdge m n) (hef : e ≠ f) :
    (a e.1,b e.2) ≠ (a f.1,b f.2) := by
  intro he
  exact hef (Prod.ext (hai (congrArg Prod.fst he)) (hbi (congrArg Prod.snd he)))

theorem axisContinuousDrawing_pair_subsingleton (a : Fin m → ℝ) (b : Fin n → ℝ)
    (hai : Function.Injective a) (hbi : Function.Injective b)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ p, b p ≠ 0) (e f : BipartiteEdge m n) (hef : e ≠ f) :
    (edgeInterior (axisContinuousDrawing a b hai hbi ha hb) e ∩
      edgeInterior (axisContinuousDrawing a b hai hbi ha hb) f).Subsingleton := by
  rw [axisContinuousDrawing_interior,axisContinuousDrawing_interior]
  exact axis_open_intersection_subsingleton _ _ _ _ (ha e.1) (hb e.2) (axis_intercept_pair_ne a b hai hbi e f hef)

theorem axisContinuousDrawing_crossings_finite (a : Fin m → ℝ) (b : Fin n → ℝ)
    (hai : Function.Injective a) (hbi : Function.Injective b)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ p, b p ≠ 0) :
    (crossingPoints (axisContinuousDrawing a b hai hbi ha hb)).Finite := by
  classical
  let D := axisContinuousDrawing a b hai hbi ha hb
  let S := fun e f : BipartiteEdge m n => if e=f then (∅ : Set Plane) else edgeInterior D e ∩ edgeInterior D f
  have hfinite (e f : BipartiteEdge m n) : (S e f).Finite := by
    dsimp only [S]
    split_ifs with hef
    · exact Set.finite_empty
    · exact (axisContinuousDrawing_pair_subsingleton a b hai hbi ha hb e f hef).finite
  apply (Set.finite_iUnion fun e => Set.finite_iUnion (hfinite e)).subset
  rintro x ⟨e,f,hef,hxe,hxf⟩
  refine Set.mem_iUnion.mpr ⟨e,Set.mem_iUnion.mpr ⟨f,?_⟩⟩
  simpa only [S,ite_eq_right hef] using (show x ∈ edgeInterior D e ∩ edgeInterior D f from ⟨hxe,hxf⟩)

theorem axisContinuousDrawing_crossings_proper (a : Fin m → ℝ) (b : Fin n → ℝ)
    (hai : Function.Injective a) (hbi : Function.Injective b)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ p, b p ≠ 0) (e f : BipartiteEdge m n) (hef : e ≠ f)
    (x : Plane) (hx : x ∈ edgeInterior (axisContinuousDrawing a b hai hbi ha hb) e)
    (hy : x ∈ edgeInterior (axisContinuousDrawing a b hai hbi ha hb) f) :
    ProperCrossing (edgeInterior (axisContinuousDrawing a b hai hbi ha hb) e)
      (edgeInterior (axisContinuousDrawing a b hai hbi ha hb) f) x := by
  rw [axisContinuousDrawing_interior] at hx hy ⊢
  rw [axisContinuousDrawing_interior]
  exact axisSegmentPoint_meeting_proper _ _ _ _ (ha e.1) (hb e.2)
    (axis_intercept_pair_ne a b hai hbi e f hef) x hx hy

end Zarankiewicz

end

end OAI
