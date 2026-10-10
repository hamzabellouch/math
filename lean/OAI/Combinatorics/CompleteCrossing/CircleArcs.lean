import OAI.Combinatorics.CompleteCrossing.Hill
import OAI.Combinatorics.CompleteCrossing.Plane
import OAI.Combinatorics.Crossing.CircleChords
import OAI.Combinatorics.Crossing.ProperCrossingLocality
import OAI.Combinatorics.Crossing.ProperSegmentCrossing
import OAI.Combinatorics.Crossing.RoundCircleChords
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Topology.OpenPartialHomeomorph.Composition

namespace OAI

/-! Circle segments, inversion, continuous paths, and admissibility of two-page arcs. -/

section

/-! Exact circle and inversion routes for the source's two-page drawing.

 -/

noncomputable section
open Set
open scoped Classical

namespace Paper170

def chordInterior {n : ℕ} (p : Fin n → Plane) (e : CompleteEdge n) : Set Plane :=
  (segmentPoint (p e.val.1) (p e.val.2)) '' Ioo (0 : ℝ) 1

/-- The source's generic circle placement, stated only in geometric terms. -/
structure CircleConfiguration (n : ℕ) where
  point : Fin n → Plane
  injective : Function.Injective point
  on_circle : ∀ i, squaredLength (point i) = 1
  cyclic_order : ∀ i j k, i < j → j < k →
    0 < det2 (point j - point i) (point k - point i)
  no_antipodal : ∀ i j, i ≠ j → point i + point j ≠ 0
  no_triple_chords : ∀ e f g : CompleteEdge n, e ≠ f → e ≠ g → f ≠ g →
    chordInterior point e ∩ chordInterior point f ∩ chordInterior point g = ∅

def twoPageRoute {n : ℕ} (C : CircleConfiguration n) (e : CompleteEdge n)
    (t : unitInterval) : Plane :=
  let x := segmentPoint (C.point e.val.1) (C.point e.val.2) t.val
  if residueColor n (e.val.1.val + e.val.2.val) then x else inversion x

/-- Equality with the actual circle/chord/inversion construction. -/
structure TwoPageDrawing {n : ℕ} (C : CircleConfiguration n)
    (D : AdmissibleDrawing (completeGraph n)) : Prop where
  vertex_eq : D.vertex = C.point
  edge_eq : ∀ e t, D.edge e t = twoPageRoute C e t

def lineIntersectionPoint (a b c d : Plane) : Plane :=
  a + (det2 (c - a) (d - c) / det2 (b - a) (d - c)) • (b - a)

def crossingTuplePoint {n : ℕ} (C : CircleConfiguration n) (v : Fin 4 → Fin n) : Plane :=
  let x := lineIntersectionPoint (C.point (v 0)) (C.point (v 2))
    (C.point (v 1)) (C.point (v 3))
  if residueColor n ((v 0).val + (v 2).val) then x else inversion x

end Paper170

end
end

section

noncomputable section
open Set
namespace Paper170

theorem chordInterior_eq_unitIntervalImage {n : ℕ} (p : Fin n → Plane) (e : CompleteEdge n) :
    chordInterior p e =
      (fun t : unitInterval => segmentPoint (p e.val.1) (p e.val.2) t.val) ''
        Ioo (0 : unitInterval) 1 := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨⟨t, ht.1.le, ht.2.le⟩, ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t.val, ht, rfl⟩

theorem twoPageRoute_image {n : ℕ} (C : CircleConfiguration n) (e : CompleteEdge n) :
    twoPageRoute C e '' Ioo (0 : unitInterval) 1 =
      if residueColor n (e.val.1.val + e.val.2.val) then chordInterior C.point e
      else inversion '' chordInterior C.point e := by
  change (fun t => twoPageRoute C e t) '' _ = _
  cases hc : residueColor n (e.val.1.val + e.val.2.val) <;>
    simp [twoPageRoute, hc, chordInterior_eq_unitIntervalImage, Set.image_image]

theorem twoPage_edgeInterior {n : ℕ} (C : CircleConfiguration n)
    (D : AdmissibleDrawing (completeGraph n)) (hD : TwoPageDrawing C D)
    (e : CompleteEdge n) :
    edgeInterior D.toContinuousDrawing e =
      if residueColor n (e.val.1.val + e.val.2.val) then chordInterior C.point e
      else inversion '' chordInterior C.point e := by
  change (D.edge e : unitInterval → Plane) '' _ = _
  rw [show (D.edge e : unitInterval → Plane) = twoPageRoute C e from funext (hD.edge_eq e)]
  exact twoPageRoute_image C e

end Paper170

end
end

section

noncomputable section
open Set
open scoped Classical
namespace Paper170

theorem circle_points_noncollinear {n : ℕ} (p : Fin n → Plane)
    (hp : Function.Injective p) (hc : ∀ i, squaredLength (p i) = 1)
    {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Zarankiewicz.orient2 (p i) (p j) (p k) ≠ 0 := by
  apply Zarankiewicz.round_circle_orient_ne_zero 0 (p i) (p j) (p k) 1
  · simpa only [sub_zero, one_pow, squaredLength, Zarankiewicz.squaredLength] using hc i
  · simpa only [sub_zero, one_pow, squaredLength, Zarankiewicz.squaredLength] using hc j
  · simpa only [sub_zero, one_pow, squaredLength, Zarankiewicz.squaredLength] using hc k
  · exact hp.ne hij
  · exact hp.ne hik
  · exact hp.ne hjk

theorem open_chord_reverse {a b x : Plane} (hx : x ∈ Zarankiewicz.openSegmentTrace a b) :
    x ∈ Zarankiewicz.openSegmentTrace b a := by
  obtain ⟨t, ht, rfl⟩ := hx
  exact ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩,
    Zarankiewicz.segmentPoint_reverse a b t⟩

theorem open_chords_common_start {a b c x : Plane}
    (hn : Zarankiewicz.orient2 a b c ≠ 0)
    (hx : x ∈ Zarankiewicz.openSegmentTrace a b)
    (hy : x ∈ Zarankiewicz.openSegmentTrace a c) : False := by
  obtain ⟨t, ht, he⟩ := hx
  obtain ⟨u, hu, hf⟩ := hy
  have hz := congrArg (Zarankiewicz.orient2 a b) (he.trans hf.symm)
  rw [Zarankiewicz.orient2_self_segment, Zarankiewicz.orient2_segment] at hz
  have ha : Zarankiewicz.orient2 a b a = 0 := by simp [Zarankiewicz.orient2, Zarankiewicz.det2]
  rw [ha, mul_zero, zero_add] at hz
  exact hn ((mul_eq_zero.mp hz.symm).resolve_left (ne_of_gt hu.1))

theorem circle_chord_endpoints_distinct {n : ℕ} (p : Fin n → Plane)
    (hp : Function.Injective p) (hc : ∀ i, squaredLength (p i) = 1)
    (e f : CompleteEdge n) (hef : e ≠ f) (x : Plane)
    (he : x ∈ chordInterior p e) (hf : x ∈ chordInterior p f) :
    e.val.1 ≠ f.val.1 ∧ e.val.1 ≠ f.val.2 ∧ e.val.2 ≠ f.val.1 ∧ e.val.2 ≠ f.val.2 := by
  have he' : x ∈ Zarankiewicz.openSegmentTrace (p e.val.1) (p e.val.2) := he
  have hf' : x ∈ Zarankiewicz.openSegmentTrace (p f.val.1) (p f.val.2) := hf
  have hei : e.val.1 < e.val.2 := e.property
  have hfi : f.val.1 < f.val.2 := f.property
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have hother : e.val.2 ≠ f.val.2 := by
      intro hh
      exact hef (Subtype.ext (Prod.ext h hh))
    have hn := circle_points_noncollinear p hp hc (ne_of_lt hei)
      (show e.val.1 ≠ f.val.2 by rw [h]; exact ne_of_lt hfi) hother
    rw [← h] at hf'
    exact open_chords_common_start hn he' hf'
  · intro h
    have hn := circle_points_noncollinear p hp hc (ne_of_lt hei)
      (show e.val.1 ≠ f.val.1 by rw [h]; exact ne_of_gt hfi) (by omega)
    have hf'' := open_chord_reverse hf'
    rw [← h] at hf''
    exact open_chords_common_start hn he' hf''
  · intro h
    have hn := circle_points_noncollinear p hp hc (ne_of_gt hei)
      (show e.val.2 ≠ f.val.2 by rw [h]; exact ne_of_lt hfi) (by omega)
    have he'' := open_chord_reverse he'
    rw [← h] at hf'
    exact open_chords_common_start hn he'' hf'
  · intro h
    have hother : e.val.1 ≠ f.val.1 := by
      intro hh
      exact hef (Subtype.ext (Prod.ext hh h))
    have hn := circle_points_noncollinear p hp hc (ne_of_gt hei)
      (show e.val.2 ≠ f.val.1 by rw [h]; exact ne_of_gt hfi) hother
    have he'' := open_chord_reverse he'
    have hf'' := open_chord_reverse hf'
    rw [← h] at hf''
    exact open_chords_common_start hn he'' hf''

end Paper170

end
end

section

noncomputable section
open Set
open scoped Classical
namespace Paper170

theorem CircleConfiguration.orient_inside {n : ℕ} (C : CircleConfiguration n)
    {i j k : Fin n} (hik : i < k) (hkj : k < j) :
    Zarankiewicz.orient2 (C.point i) (C.point j) (C.point k) < 0 := by
  rw [Zarankiewicz.orient2_swap_ends]
  exact neg_neg_of_pos (C.cyclic_order i k j hik hkj)

theorem CircleConfiguration.orient_outside {n : ℕ} (C : CircleConfiguration n)
    {i j k : Fin n} (hij : i < j) (hk : k < i ∨ j < k) :
    0 < Zarankiewicz.orient2 (C.point i) (C.point j) (C.point k) := by
  rcases hk with hk | hk
  · rw [Zarankiewicz.orient2_cycle (C.point k) (C.point i) (C.point j)]
    exact C.cyclic_order k i j hk hij
  · exact C.cyclic_order i j k hij hk

theorem CircleConfiguration.alternating_cross {n : ℕ} (C : CircleConfiguration n)
    {i k j l : Fin n} (hik : i < k) (hkj : k < j) (hjl : j < l) :
    Zarankiewicz.SegmentsCrossProperly (C.point i) (C.point j) (C.point k) (C.point l) := by
  have hsign := Zarankiewicz.segmentCrossingSign_of_positive_sides
    (C.point i) (C.point j) (C.point k) (C.point l)
    (C.orient_inside hik hkj) (C.orient_outside (hik.trans hkj) (Or.inr hjl))
    (C.orient_outside (hkj.trans hjl) (Or.inl hik)) (C.orient_inside hkj hjl)
  by_contra h
  simp [Zarankiewicz.segmentCrossingSign, h] at hsign

theorem lineIntersectionPoint_eq_parameter (a b c d : Plane) :
    lineIntersectionPoint a b c d =
      Zarankiewicz.segmentPoint a b (Zarankiewicz.firstIntersectionParameter a b c d) := by
  have hnum : det2 (c - a) (d - c) = Zarankiewicz.det2 (d - c) (a - c) := by
    dsimp [det2, Zarankiewicz.det2]
    ring
  unfold lineIntersectionPoint
  rw [hnum]
  change a + Zarankiewicz.firstIntersectionParameter a b c d • (b - a) = _
  ext <;> simp [Zarankiewicz.segmentPoint] <;> ring

theorem open_chords_intersection_singleton (a b c d : Plane)
    (h : Zarankiewicz.SegmentsCrossProperly a b c d) :
    Zarankiewicz.openSegmentTrace a b ∩ Zarankiewicz.openSegmentTrace c d =
      {lineIntersectionPoint a b c d} := by
  have ht := (Zarankiewicz.segmentsCrossProperly_iff_parameters a b c d h.1).mp h
  have hp : lineIntersectionPoint a b c d ∈
      Zarankiewicz.openSegmentTrace a b ∩ Zarankiewicz.openSegmentTrace c d := by
    rw [lineIntersectionPoint_eq_parameter]
    exact ⟨⟨_, ht.1, rfl⟩, ⟨_, ht.2, (Zarankiewicz.intersection_parameters_eq a b c d h.1).symm⟩⟩
  ext x
  constructor
  · intro hx
    exact (Zarankiewicz.openSegment_intersection_subsingleton a b c d h.1 hx hp)
  · rintro rfl
    exact hp

theorem circle_chord_intersection {n : ℕ} (C : CircleConfiguration n)
    (e f : CompleteEdge n) (hef : e ≠ f) :
    chordInterior C.point e ∩ chordInterior C.point f =
      if (e.val.1 < f.val.1 ∧ f.val.1 < e.val.2 ∧ e.val.2 < f.val.2) ∨
         (f.val.1 < e.val.1 ∧ e.val.1 < f.val.2 ∧ f.val.2 < e.val.2) then
        {lineIntersectionPoint (C.point e.val.1) (C.point e.val.2)
          (C.point f.val.1) (C.point f.val.2)}
      else ∅ := by
  by_cases halt : (e.val.1 < f.val.1 ∧ f.val.1 < e.val.2 ∧ e.val.2 < f.val.2) ∨
      (f.val.1 < e.val.1 ∧ e.val.1 < f.val.2 ∧ f.val.2 < e.val.2)
  · rw [ite_eq_left halt]
    apply open_chords_intersection_singleton
    rcases halt with ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩
    · exact C.alternating_cross h₁ h₂ h₃
    · exact (Zarankiewicz.segmentsCrossProperly_swap _ _ _ _).mp
        (C.alternating_cross h₁ h₂ h₃)
  · rw [ite_eq_right halt]
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨h02, h03, h12, h13⟩ := circle_chord_endpoints_distinct C.point C.injective
      C.on_circle e f hef x hx.1 hx.2
    have hei := e.property
    have hfi := f.property
    have htrans := Zarankiewicz.round_circle_chords_transverse 0
      (C.point e.val.1) (C.point e.val.2) (C.point f.val.1) (C.point f.val.2) 1
      (by simpa only [sub_zero, one_pow, squaredLength, Zarankiewicz.squaredLength] using C.on_circle e.val.1)
      (by simpa only [sub_zero, one_pow, squaredLength, Zarankiewicz.squaredLength] using C.on_circle e.val.2)
      (by simpa only [sub_zero, one_pow, squaredLength, Zarankiewicz.squaredLength] using C.on_circle f.val.1)
      (by simpa only [sub_zero, one_pow, squaredLength, Zarankiewicz.squaredLength] using C.on_circle f.val.2)
      (C.injective.ne (ne_of_lt hei)) (C.injective.ne (ne_of_lt hfi))
      (C.injective.ne h02) (C.injective.ne h03) (C.injective.ne h12) (C.injective.ne h13)
    obtain ⟨t, ht, he⟩ := hx.1
    obtain ⟨u, hu, hf⟩ := hx.2
    have heq := he.trans hf.symm
    have hcross : Zarankiewicz.SegmentsCrossProperly (C.point e.val.1) (C.point e.val.2)
        (C.point f.val.1) (C.point f.val.2) :=
      ⟨(htrans t ⟨ht.1.le, ht.2.le⟩ u ⟨hu.1.le, hu.2.le⟩ heq).1, t, ht, u, hu, heq⟩
    apply Zarankiewicz.not_segmentsCrossProperly_of_same_side _ _ _ _ _ hcross
    by_cases hinside : e.val.1 < f.val.1 ∧ f.val.1 < e.val.2
    · exact Or.inr ⟨C.orient_inside hinside.1 hinside.2,
        C.orient_inside (by omega) (by omega)⟩
    · exact Or.inl ⟨C.orient_outside hei (by omega), C.orient_outside hei (by omega)⟩

end Paper170

end
end

section

noncomputable section
open Set
open scoped Classical
namespace Paper170

@[simp] theorem inversion_zero : inversion 0 = 0 := by
  simp [inversion, squaredLength]

theorem inversion_ne_zero {x : Plane} (hx : x ≠ 0) : inversion x ≠ 0 := by
  intro h
  exact hx ((inversion_involutive x).symm.trans ((congrArg inversion h).trans inversion_zero))

theorem continuous_squaredLength : Continuous squaredLength := by
  unfold squaredLength
  fun_prop

theorem continuousAt_inversion {x : Plane} (hx : x ≠ 0) : ContinuousAt inversion x := by
  have hq := ne_of_gt (squaredLength_pos hx)
  exact (continuous_fst.continuousAt.div continuous_squaredLength.continuousAt hq).prodMk
    (continuous_snd.continuousAt.div continuous_squaredLength.continuousAt hq)

def inversionChart : OpenPartialHomeomorph Plane Plane where
  toFun := inversion
  invFun := inversion
  source := {x | x ≠ 0}
  target := {x | x ≠ 0}
  map_source' := fun _ hx => inversion_ne_zero hx
  map_target' := fun _ hx => inversion_ne_zero hx
  left_inv' := fun x _ => inversion_involutive x
  right_inv' := fun x _ => inversion_involutive x
  continuousOn_toFun := fun _ hx => (continuousAt_inversion hx).continuousWithinAt
  continuousOn_invFun := fun _ hx => (continuousAt_inversion hx).continuousWithinAt
  open_source := isClosed_singleton.isOpen_compl
  open_target := isClosed_singleton.isOpen_compl

theorem inversion_chart_image (c : OpenPartialHomeomorph Plane Plane) (A L : Set Plane)
    (h : c '' (c.source ∩ A) = c.target ∩ L) :
    (inversionChart.trans c) '' ((inversionChart.trans c).source ∩ inversion '' A) =
      (inversionChart.trans c).target ∩ L := by
  let e := inversionChart.trans c
  apply Set.Subset.antisymm
  · rintro y ⟨z, hz, rfl⟩
    have hs : z ≠ 0 ∧ inversion z ∈ c.source := hz.1
    obtain ⟨a, ha, rfl⟩ := hz.2
    have hi : inversion (inversion a) ∈ A := (inversion_involutive a).symm ▸ ha
    exact ⟨e.map_source hz.1,
      (Zarankiewicz.chart_image_mem_iff c A L h _ hs.2).mp hi⟩
  · rintro y ⟨hy, hL⟩
    have hz := e.map_target hy
    have hs : e.symm y ≠ 0 ∧ inversion (e.symm y) ∈ c.source := hz
    have he : c (inversion (e.symm y)) = y := e.right_inv hy
    have ha : inversion (e.symm y) ∈ A :=
      (Zarankiewicz.chart_image_mem_iff c A L h _ hs.2).mpr (he.symm ▸ hL)
    exact ⟨e.symm y, ⟨hz, ⟨inversion (e.symm y), ha, inversion_involutive _⟩⟩,
      e.right_inv hy⟩

theorem ProperCrossing.inverted {A B : Set Plane} {x : Plane}
    (h : ProperCrossing A B x) (hx : x ≠ 0) :
    ProperCrossing (inversion '' A) (inversion '' B) (inversion x) := by
  obtain ⟨c, hs, he, hA, hB⟩ := h.chart_exists
  refine ⟨inversionChart.trans c, ⟨inversion_ne_zero hx, ?_⟩, ?_,
    inversion_chart_image c A _ hA, inversion_chart_image c B _ hB⟩
  · change inversion (inversion x) ∈ c.source
    rwa [inversion_involutive]
  · change c (inversion (inversion x)) = (0, 0)
    rwa [inversion_involutive]

theorem squaredLength_inversion {x : Plane} (hx : x ≠ 0) :
    squaredLength (inversion x) = (squaredLength x)⁻¹ := by
  have hq := ne_of_gt (squaredLength_pos hx)
  change (x.1 / squaredLength x)^2 + (x.2 / squaredLength x)^2 = _
  rw [div_pow, div_pow, ← add_div]
  change squaredLength x / squaredLength x ^ 2 = _
  field_simp

theorem chord_ne_zero {a b : Plane} (ha : squaredLength a = 1)
    (hb : squaredLength b = 1) (hab : a + b ≠ 0) (t : ℝ) :
    segmentPoint a b t ≠ 0 := by
  intro h
  have h0 := congrArg Prod.fst h
  have h1 := congrArg Prod.snd h
  change (1-t)*a.1+t*b.1=0 at h0
  change (1-t)*a.2+t*b.2=0 at h1
  have ht : t = 1/2 := by
    have he : (1-t)^2 * squaredLength a = t^2 * squaredLength b := by
      unfold squaredLength
      linear_combination ((1-t)*a.1-t*b.1)*h0 + ((1-t)*a.2-t*b.2)*h1
    rw [ha, hb] at he
    nlinarith
  apply hab
  ext <;> dsimp <;> rw [ht] at h0 h1 <;> linarith

theorem CircleConfiguration.chord_ne_zero {n : ℕ} (C : CircleConfiguration n)
    (e : CompleteEdge n) (t : ℝ) :
    segmentPoint (C.point e.val.1) (C.point e.val.2) t ≠ 0 :=
  Paper170.chord_ne_zero (C.on_circle _) (C.on_circle _)
    (C.no_antipodal _ _ (ne_of_lt e.property)) t

theorem CircleConfiguration.chord_inside {n : ℕ} (C : CircleConfiguration n)
    (e : CompleteEdge n) {x : Plane} (hx : x ∈ chordInterior C.point e) :
    squaredLength x < 1 := by
  obtain ⟨t, ht, rfl⟩ := hx
  simpa only [squaredLength, Zarankiewicz.squaredLength, sub_zero, one_pow, segmentPoint_eq] using
    Zarankiewicz.round_chord_in_open_disk 0 (C.point e.val.1) (C.point e.val.2) 1
      (by simpa only [squaredLength, Zarankiewicz.squaredLength, sub_zero, one_pow] using C.on_circle e.val.1)
      (by simpa only [squaredLength, Zarankiewicz.squaredLength, sub_zero, one_pow] using C.on_circle e.val.2)
      (C.injective.ne (ne_of_lt e.property)) t ht

theorem CircleConfiguration.chord_mem_ne_zero {n : ℕ} (C : CircleConfiguration n)
    (e : CompleteEdge n) {x : Plane} (hx : x ∈ chordInterior C.point e) : x ≠ 0 := by
  obtain ⟨t, _, rfl⟩ := hx
  exact C.chord_ne_zero e t

theorem CircleConfiguration.inverted_chord_outside {n : ℕ} (C : CircleConfiguration n)
    (e : CompleteEdge n) {x : Plane} (hx : x ∈ inversion '' chordInterior C.point e) :
    1 < squaredLength x := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [squaredLength_inversion (C.chord_mem_ne_zero e hy)]
  exact (one_lt_inv₀ (squaredLength_pos (C.chord_mem_ne_zero e hy))).mpr (C.chord_inside e hy)

end Paper170

end
end

section

noncomputable section
open Set
open scoped Classical
namespace Paper170

theorem segmentPoint_injective {a b : Plane} (hab : a ≠ b) :
    Function.Injective (segmentPoint a b) := by
  intro s t h
  apply AffineMap.lineMap_injective ℝ hab
  simpa only [AffineMap.lineMap_apply_module, segmentPoint] using h

theorem continuous_segmentPoint (a b : Plane) : Continuous (segmentPoint a b) := by
  unfold segmentPoint
  fun_prop

theorem continuous_twoPageRoute {n : ℕ} (C : CircleConfiguration n) (e : CompleteEdge n) :
    Continuous (twoPageRoute C e) := by
  have hseg : Continuous (fun t : unitInterval => segmentPoint (C.point e.val.1) (C.point e.val.2) t.val) :=
    (continuous_segmentPoint _ _).comp continuous_subtype_val
  change Continuous (fun t => twoPageRoute C e t)
  cases hc : residueColor n (e.val.1.val + e.val.2.val)
  ·
    simp only [twoPageRoute, hc, Bool.false_eq_true, ↓reduceIte]
    exact continuous_iff_continuousAt.mpr (fun t =>
      (continuousAt_inversion (C.chord_ne_zero e t.val)).comp
        (f := fun u : unitInterval => segmentPoint (C.point e.val.1) (C.point e.val.2) u.val)
        hseg.continuousAt)
  · simpa only [twoPageRoute, hc, ↓reduceIte] using hseg

def twoPagePath {n : ℕ} (C : CircleConfiguration n) (e : CompleteEdge n) :
    Path (C.point e.val.1) (C.point e.val.2) where
  toFun := twoPageRoute C e
  continuous_toFun := continuous_twoPageRoute C e
  source' := by
    simp [twoPageRoute, segmentPoint, inversion_fixes_circle _ (C.on_circle _)]
  target' := by
    simp [twoPageRoute, segmentPoint, inversion_fixes_circle _ (C.on_circle _)]

theorem twoPageRoute_injective {n : ℕ} (C : CircleConfiguration n) (e : CompleteEdge n) :
    Function.Injective (twoPageRoute C e) := by
  have hseg := (segmentPoint_injective (C.injective.ne (ne_of_lt e.property))).comp
    (show Function.Injective (fun t : unitInterval => t.val) from Subtype.val_injective)
  cases hc : residueColor n (e.val.1.val + e.val.2.val)
  · intro s t h
    apply hseg
    change segmentPoint (C.point e.val.1) (C.point e.val.2) s.val =
      segmentPoint (C.point e.val.1) (C.point e.val.2) t.val
    exact inversion_involutive.injective (by simpa only [twoPageRoute, hc, Bool.false_eq_true, ↓reduceIte] using h)
  · intro s t h
    apply hseg
    change segmentPoint (C.point e.val.1) (C.point e.val.2) s.val =
      segmentPoint (C.point e.val.1) (C.point e.val.2) t.val
    simpa only [twoPageRoute, hc, ↓reduceIte] using h

theorem twoPageRoute_avoids_vertices {n : ℕ} (C : CircleConfiguration n)
    (e : CompleteEdge n) (t : unitInterval) (ht : t ∈ Ioo (0 : unitInterval) 1) (v : Fin n) :
    twoPageRoute C e t ≠ C.point v := by
  have hmem : twoPageRoute C e t ∈ twoPageRoute C e '' Ioo (0 : unitInterval) 1 := ⟨t, ht, rfl⟩
  rw [twoPageRoute_image] at hmem
  intro he
  rw [he] at hmem
  cases hc : residueColor n (e.val.1.val + e.val.2.val)
  · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hmem
    have h := C.inverted_chord_outside e hmem
    rw [C.on_circle] at h
    exact (lt_irrefl _ h)
  · simp only [hc, ↓reduceIte] at hmem
    have h := C.chord_inside e hmem
    rw [C.on_circle] at h
    exact (lt_irrefl _ h)

def twoPageContinuous {n : ℕ} (C : CircleConfiguration n) :
    ContinuousDrawing (completeGraph n) where
  vertex := C.point
  vertex_injective := C.injective
  edge := twoPagePath C
  edge_injective := twoPageRoute_injective C
  interior_avoids_vertices := twoPageRoute_avoids_vertices C

theorem twoPageContinuous_edgeInterior {n : ℕ} (C : CircleConfiguration n) (e : CompleteEdge n) :
    edgeInterior (twoPageContinuous C) e =
      if residueColor n (e.val.1.val + e.val.2.val) then chordInterior C.point e
      else inversion '' chordInterior C.point e :=
  twoPageRoute_image C e

end Paper170

end
end

section

noncomputable section
open Set
open scoped Classical
namespace Paper170

theorem CircleConfiguration.chord_proper {n : ℕ} (C : CircleConfiguration n)
    (e f : CompleteEdge n) (hef : e ≠ f) {x : Plane}
    (hx : x ∈ chordInterior C.point e) (hy : x ∈ chordInterior C.point f) :
    ProperCrossing (chordInterior C.point e) (chordInterior C.point f) x := by
  have hp : x ∈ chordInterior C.point e ∩ chordInterior C.point f := ⟨hx, hy⟩
  rw [circle_chord_intersection C e f hef] at hp
  split_ifs at hp with halt
  · have hcross : Zarankiewicz.SegmentsCrossProperly (C.point e.val.1) (C.point e.val.2)
        (C.point f.val.1) (C.point f.val.2) := by
      rcases halt with ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩
      · exact C.alternating_cross h₁ h₂ h₃
      · exact (Zarankiewicz.segmentsCrossProperly_swap _ _ _ _).mp (C.alternating_cross h₁ h₂ h₃)
    exact ⟨Zarankiewicz.properCrossing_openSegments _ _ _ _ x hcross.1 hx hy⟩
  · exact hp.elim

theorem CircleConfiguration.chord_inter_finite {n : ℕ} (C : CircleConfiguration n)
    (e f : CompleteEdge n) (hef : e ≠ f) :
    (chordInterior C.point e ∩ chordInterior C.point f).Finite := by
  rw [circle_chord_intersection C e f hef]
  split_ifs <;> simp

theorem CircleConfiguration.chord_inverted_disjoint {n : ℕ} (C : CircleConfiguration n)
    (e f : CompleteEdge n) :
    Disjoint (chordInterior C.point e) (inversion '' chordInterior C.point f) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact lt_asymm (C.chord_inside e hx) (C.inverted_chord_outside f hy)

theorem twoPageContinuous_same_color {n : ℕ} (C : CircleConfiguration n)
    (e f : CompleteEdge n) {x : Plane}
    (hx : x ∈ edgeInterior (twoPageContinuous C) e)
    (hy : x ∈ edgeInterior (twoPageContinuous C) f) :
    residueColor n (e.val.1.val + e.val.2.val) =
      residueColor n (f.val.1.val + f.val.2.val) := by
  rw [twoPageContinuous_edgeInterior] at hx hy
  cases he : residueColor n (e.val.1.val + e.val.2.val) <;>
    cases hf : residueColor n (f.val.1.val + f.val.2.val) <;>
    simp only [he, hf, Bool.false_eq_true, ↓reduceIte] at hx hy ⊢
  · exact (lt_asymm (C.inverted_chord_outside e hx) (C.chord_inside f hy)).elim
  · exact (lt_asymm (C.chord_inside e hx) (C.inverted_chord_outside f hy)).elim

theorem twoPageContinuous_inter_finite {n : ℕ} (C : CircleConfiguration n)
    (e f : CompleteEdge n) (hef : e ≠ f) :
    (edgeInterior (twoPageContinuous C) e ∩ edgeInterior (twoPageContinuous C) f).Finite := by
  rw [twoPageContinuous_edgeInterior, twoPageContinuous_edgeInterior]
  cases he : residueColor n (e.val.1.val + e.val.2.val) <;>
    cases hf : residueColor n (f.val.1.val + f.val.2.val) <;>
    simp only [Bool.false_eq_true, ↓reduceIte]
  · rw [← Set.image_inter inversion_involutive.injective]
    exact (C.chord_inter_finite e f hef).image _
  · rw [(C.chord_inverted_disjoint f e).symm.inter_eq]
    exact Set.finite_empty
  · rw [(C.chord_inverted_disjoint e f).inter_eq]
    exact Set.finite_empty
  · exact C.chord_inter_finite e f hef

theorem twoPageContinuous_crossings_finite {n : ℕ} (C : CircleConfiguration n) :
    (crossingPoints (twoPageContinuous C)).Finite := by
  have heq : crossingPoints (twoPageContinuous C) =
      ⋃ e : CompleteEdge n, ⋃ f : CompleteEdge n,
        if e = f then ∅ else edgeInterior (twoPageContinuous C) e ∩
          edgeInterior (twoPageContinuous C) f := by
    ext x
    simp only [crossingPoints, mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨e, f, hef, hx, hy⟩
      exact ⟨e, f, by rw [ite_eq_right hef]; exact ⟨hx, hy⟩⟩
    · rintro ⟨e, f, hx⟩
      split_ifs at hx with hef
      · exact hx.elim
      · exact ⟨e, f, hef, hx.1, hx.2⟩
  rw [heq]
  apply Set.finite_iUnion
  intro e
  apply Set.finite_iUnion
  intro f
  split_ifs with hef
  · exact Set.finite_empty
  · exact twoPageContinuous_inter_finite C e f hef

theorem twoPageContinuous_proper {n : ℕ} (C : CircleConfiguration n)
    (e f : CompleteEdge n) (hef : e ≠ f) (x : Plane)
    (hx : x ∈ edgeInterior (twoPageContinuous C) e)
    (hy : x ∈ edgeInterior (twoPageContinuous C) f) :
    ProperCrossing (edgeInterior (twoPageContinuous C) e)
      (edgeInterior (twoPageContinuous C) f) x := by
  have hc := twoPageContinuous_same_color C e f hx hy
  simp only [twoPageContinuous_edgeInterior] at hx hy ⊢
  rw [hc] at hx ⊢
  cases hf : residueColor n (f.val.1.val + f.val.2.val) <;>
    simp only [hf, Bool.false_eq_true, ↓reduceIte] at hx hy ⊢
  · obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, he⟩ := hy
    have hba : b = a := inversion_involutive.injective he
    subst b
    exact (C.chord_proper e f hef ha hb).inverted (C.chord_mem_ne_zero e ha)
  · exact C.chord_proper e f hef hx hy

theorem twoPageContinuous_no_triples {n : ℕ} (C : CircleConfiguration n)
    (e f g : CompleteEdge n) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) :
    edgeInterior (twoPageContinuous C) e ∩ edgeInterior (twoPageContinuous C) f ∩
      edgeInterior (twoPageContinuous C) g = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hcf := twoPageContinuous_same_color C e f hx.1.1 hx.1.2
  have hcg := twoPageContinuous_same_color C e g hx.1.1 hx.2
  simp only [twoPageContinuous_edgeInterior, ← hcf, ← hcg] at hx
  cases he : residueColor n (e.val.1.val + e.val.2.val) <;>
    simp only [he, Bool.false_eq_true, ↓reduceIte] at hx
  · have hm : x ∈ inversion ''
        (chordInterior C.point e ∩ chordInterior C.point f ∩ chordInterior C.point g) := by
      rw [Set.image_inter inversion_involutive.injective,
        Set.image_inter inversion_involutive.injective]
      exact hx
    rw [C.no_triple_chords e f g hef heg hfg, Set.image_empty] at hm
    exact hm.elim
  · rw [C.no_triple_chords e f g hef heg hfg] at hx
    exact hx.elim

def twoPageAdmissible {n : ℕ} (C : CircleConfiguration n) :
    AdmissibleDrawing (completeGraph n) where
  toContinuousDrawing := twoPageContinuous C
  crossings_finite := twoPageContinuous_crossings_finite C
  crossings_proper := twoPageContinuous_proper C
  no_triples := twoPageContinuous_no_triples C

theorem two_page_drawing_exists {n : ℕ} (C : CircleConfiguration n) :
    ∃ D : AdmissibleDrawing (completeGraph n), TwoPageDrawing C D :=
  ⟨twoPageAdmissible C, rfl, fun _ _ => rfl⟩

end Paper170

end
end

end OAI
