import OAI.Combinatorics.CompleteCrossing.CirclePlacement
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

namespace OAI

/-! Counting actual crossing points of the explicit two-page drawing. -/

section

noncomputable section
open Set
open scoped Classical
namespace Paper170

lemma twoPage_meeting_chords {n : ℕ} (C : CircleConfiguration n)
    (D : AdmissibleDrawing (completeGraph n)) (hD : TwoPageDrawing C D)
    (e f : CompleteEdge n) (x : Plane)
    (he : x ∈ edgeInterior D.toContinuousDrawing e)
    (hf : x ∈ edgeInterior D.toContinuousDrawing f) :
    residueColor n (e.val.1.val + e.val.2.val) = residueColor n (f.val.1.val + f.val.2.val) ∧
      ∃ y, y ∈ chordInterior C.point e ∩ chordInterior C.point f ∧
        x = if residueColor n (e.val.1.val + e.val.2.val) then y else inversion y := by
  rw [twoPage_edgeInterior C D hD e] at he
  rw [twoPage_edgeInterior C D hD f] at hf
  cases hec : residueColor n (e.val.1.val + e.val.2.val) <;>
    cases hfc : residueColor n (f.val.1.val + f.val.2.val)
  · simp only [hec, Bool.false_eq_true, ↓reduceIte] at he
    simp only [hfc, Bool.false_eq_true, ↓reduceIte] at hf
    obtain ⟨y, hy, rfl⟩ := he
    obtain ⟨z, hz, hzy⟩ := hf
    have hzy' : z = y := inversion_involutive.injective hzy
    subst z
    exact ⟨rfl, y, ⟨hy, hz⟩, rfl⟩
  · simp only [hec, Bool.false_eq_true, ↓reduceIte] at he
    simp only [hfc, ↓reduceIte] at hf
    have h1 := C.inverted_chord_outside e he
    have h2 := C.chord_inside f hf
    linarith
  · simp only [hec, ↓reduceIte] at he
    simp only [hfc, Bool.false_eq_true, ↓reduceIte] at hf
    have h1 := C.chord_inside e he
    have h2 := C.inverted_chord_outside f hf
    linarith
  · simp only [hec, ↓reduceIte] at he
    simp only [hfc, ↓reduceIte] at hf
    exact ⟨rfl, x, ⟨he, hf⟩, rfl⟩

lemma chord_meeting_alternates {n : ℕ} (C : CircleConfiguration n)
    (e f : CompleteEdge n) (hef : e ≠ f) (y : Plane)
    (hy : y ∈ chordInterior C.point e ∩ chordInterior C.point f) :
    ((e.val.1 < f.val.1 ∧ f.val.1 < e.val.2 ∧ e.val.2 < f.val.2) ∨
      (f.val.1 < e.val.1 ∧ e.val.1 < f.val.2 ∧ f.val.2 < e.val.2)) ∧
      y = lineIntersectionPoint (C.point e.val.1) (C.point e.val.2)
        (C.point f.val.1) (C.point f.val.2) := by
  rw [circle_chord_intersection C e f hef] at hy
  split_ifs at hy with h
  · exact ⟨h, hy⟩
  · exact hy.elim

lemma twoPage_meeting_alternates {n : ℕ} (C : CircleConfiguration n)
    (D : AdmissibleDrawing (completeGraph n)) (hD : TwoPageDrawing C D)
    (e f : CompleteEdge n) (hef : e ≠ f) (x : Plane)
    (he : x ∈ edgeInterior D.toContinuousDrawing e)
    (hf : x ∈ edgeInterior D.toContinuousDrawing f) :
    residueColor n (e.val.1.val + e.val.2.val) = residueColor n (f.val.1.val + f.val.2.val) ∧
    ((e.val.1 < f.val.1 ∧ f.val.1 < e.val.2 ∧ e.val.2 < f.val.2) ∨
      (f.val.1 < e.val.1 ∧ e.val.1 < f.val.2 ∧ f.val.2 < e.val.2)) ∧
    x = if residueColor n (e.val.1.val + e.val.2.val) then
      lineIntersectionPoint (C.point e.val.1) (C.point e.val.2) (C.point f.val.1) (C.point f.val.2)
      else inversion (lineIntersectionPoint (C.point e.val.1) (C.point e.val.2)
        (C.point f.val.1) (C.point f.val.2)) := by
  obtain ⟨hc, y, hy, hx⟩ := twoPage_meeting_chords C D hD e f x he hf
  obtain ⟨ho, rfl⟩ := chord_meeting_alternates C e f hef y hy
  exact ⟨hc, ho, hx⟩

lemma pagePoint_mem_edge {n : ℕ} (C : CircleConfiguration n)
    (D : AdmissibleDrawing (completeGraph n)) (hD : TwoPageDrawing C D)
    (e : CompleteEdge n) (y : Plane) (hy : y ∈ chordInterior C.point e) :
    (if residueColor n (e.val.1.val + e.val.2.val) then y else inversion y) ∈
      edgeInterior D.toContinuousDrawing e := by
  rw [twoPage_edgeInterior C D hD]
  cases h : residueColor n (e.val.1.val + e.val.2.val)
  · exact ⟨y, hy, rfl⟩
  · exact hy

lemma ordered_chord_meeting {n : ℕ} (C : CircleConfiguration n)
    (e f : CompleteEdge n)
    (ho : e.val.1 < f.val.1 ∧ f.val.1 < e.val.2 ∧ e.val.2 < f.val.2) :
    lineIntersectionPoint (C.point e.val.1) (C.point e.val.2)
      (C.point f.val.1) (C.point f.val.2) ∈ chordInterior C.point e ∩ chordInterior C.point f := by
  have hef : e ≠ f := by intro h; subst f; exact (lt_irrefl _ ho.1)
  rw [circle_chord_intersection C e f hef, ite_eq_left (Or.inl ho)]
  exact Set.mem_singleton _

end Paper170

end
end

section

noncomputable section
open Set
open scoped Classical
namespace Paper170

def tupleFirstEdge {n : ℕ} (v : Fin 4 → Fin n) (hv : StrictMono v) : CompleteEdge n :=
  ⟨(v 0, v 2), hv (by decide)⟩

def tupleSecondEdge {n : ℕ} (v : Fin 4 → Fin n) (hv : StrictMono v) : CompleteEdge n :=
  ⟨(v 1, v 3), hv (by decide)⟩

lemma tuple_edges_ne {n : ℕ} (v : Fin 4 → Fin n) (hv : StrictMono v) :
    tupleFirstEdge v hv ≠ tupleSecondEdge v hv := by
  intro h
  exact (ne_of_lt (hv (by decide : (0 : Fin 4) < 1)))
    (congrArg (fun e => e.val.1) h)

lemma tuple_point_membership {n : ℕ} (C : CircleConfiguration n)
    (D : AdmissibleDrawing (completeGraph n)) (hD : TwoPageDrawing C D)
    (v : Fin 4 → Fin n) (hv : v ∈ crossingTuples n) :
    let hm := (Finset.mem_filter.mp hv).2.1
    crossingTuplePoint C v ∈ edgeInterior D.toContinuousDrawing (tupleFirstEdge v hm) ∧
      crossingTuplePoint C v ∈ edgeInterior D.toContinuousDrawing (tupleSecondEdge v hm) := by
  let hm := (Finset.mem_filter.mp hv).2.1
  have hc := (Finset.mem_filter.mp hv).2.2
  have hy := ordered_chord_meeting C (tupleFirstEdge v hm) (tupleSecondEdge v hm)
    ⟨hm (by decide : (0 : Fin 4) < 1), hm (by decide : (1 : Fin 4) < 2),
      hm (by decide : (2 : Fin 4) < 3)⟩
  constructor
  · exact pagePoint_mem_edge C D hD (tupleFirstEdge v hm) _ hy.1
  · have h := pagePoint_mem_edge C D hD (tupleSecondEdge v hm) _ hy.2
    change (if residueColor n ((v 1).val + (v 3).val) then _ else _) ∈ _ at h
    rw [← hc] at h
    exact h

lemma ordered_pair_tuple {n : ℕ} (C : CircleConfiguration n) (e f : CompleteEdge n)
    (ho : e.val.1 < f.val.1 ∧ f.val.1 < e.val.2 ∧ e.val.2 < f.val.2)
    (hc : residueColor n (e.val.1.val + e.val.2.val) = residueColor n (f.val.1.val + f.val.2.val)) :
    ∃ v ∈ crossingTuples n, crossingTuplePoint C v =
      if residueColor n (e.val.1.val + e.val.2.val) then
        lineIntersectionPoint (C.point e.val.1) (C.point e.val.2) (C.point f.val.1) (C.point f.val.2)
      else inversion (lineIntersectionPoint (C.point e.val.1) (C.point e.val.2)
        (C.point f.val.1) (C.point f.val.2)) := by
  let v : Fin 4 → Fin n := ![e.val.1, f.val.1, e.val.2, f.val.2]
  refine ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩, rfl⟩
  · apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i
    · exact ho.1
    · exact ho.2.1
    · exact ho.2.2
  · exact hc

lemma crossingTuplePoint_surjOn {n : ℕ} (C : CircleConfiguration n)
    (D : AdmissibleDrawing (completeGraph n)) (hD : TwoPageDrawing C D) :
    SurjOn (crossingTuplePoint C) (crossingTuples n : Set (Fin 4 → Fin n))
      (crossingPoints D.toContinuousDrawing) := by
  rintro x ⟨e, f, hef, he, hf⟩
  obtain ⟨hc, ho, hx⟩ := twoPage_meeting_alternates C D hD e f hef x he hf
  rcases ho with ho | ho
  · obtain ⟨v, hv, hp⟩ := ordered_pair_tuple C e f ho hc
    exact ⟨v, hv, hp.trans hx.symm⟩
  · obtain ⟨_, _, hx'⟩ := twoPage_meeting_alternates C D hD f e hef.symm x hf he
    obtain ⟨v, hv, hp⟩ := ordered_pair_tuple C f e ho hc.symm
    exact ⟨v, hv, hp.trans hx'.symm⟩

lemma crossingTuplePoint_injOn {n : ℕ} (C : CircleConfiguration n)
    (D : AdmissibleDrawing (completeGraph n)) (hD : TwoPageDrawing C D) :
    InjOn (crossingTuplePoint C) (crossingTuples n : Set (Fin 4 → Fin n)) := by
  intro v hv w hw hpoint
  let hv' := (Finset.mem_filter.mp hv).2.1
  let hw' := (Finset.mem_filter.mp hw).2.1
  have hpv := tuple_point_membership C D hD v hv
  have hpw := tuple_point_membership C D hD w hw
  rw [← hpoint] at hpw
  have hinc := Paper170Geometry.crossing_incident_iff D (crossingTuplePoint C v)
    (tupleFirstEdge v hv') (tupleSecondEdge v hv') (tuple_edges_ne v hv') hpv.1 hpv.2
  have he := (hinc (tupleFirstEdge w hw')).mp hpw.1
  have hf := (hinc (tupleSecondEdge w hw')).mp hpw.2
  rcases he with he | he <;> rcases hf with hf | hf
  · exact (tuple_edges_ne w hw' (he.trans hf.symm)).elim
  · have h0 := congrArg (fun e => e.val.1) he
    have h2 := congrArg (fun e => e.val.2) he
    have h1 := congrArg (fun e => e.val.1) hf
    have h3 := congrArg (fun e => e.val.2) hf
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
  · have h0 : w 0 = v 1 := congrArg (fun e => e.val.1) he
    have h1 : w 1 = v 0 := congrArg (fun e => e.val.1) hf
    have hlt := hw' (by decide : (0 : Fin 4) < 1)
    rw [h0, h1] at hlt
    exact (lt_asymm (hv' (by decide : (0 : Fin 4) < 1)) hlt).elim
  · exact (tuple_edges_ne w hw' (he.trans hf.symm)).elim

theorem two_page_crossing_bijection {n : ℕ} (C : CircleConfiguration n)
    (D : AdmissibleDrawing (completeGraph n)) (hD : TwoPageDrawing C D) :
    BijOn (crossingTuplePoint C) (crossingTuples n : Set (Fin 4 → Fin n))
      (crossingPoints D.toContinuousDrawing) := by
  refine ⟨?_, crossingTuplePoint_injOn C D hD, crossingTuplePoint_surjOn C D hD⟩
  intro v hv
  have hp := tuple_point_membership C D hD v hv
  exact ⟨_, _, tuple_edges_ne _ _, hp.1, hp.2⟩

end Paper170

end
end

section

noncomputable section
namespace Paper170

theorem two_page_crossing_count {n : ℕ} (C : CircleConfiguration n)
    (D : AdmissibleDrawing (completeGraph n)) (hD : TwoPageDrawing C D) :
    crossingCount D = (crossingTuples n).card := by
  have h := (two_page_crossing_bijection C D hD).ncard_eq
  simpa [crossingCount, Set.ncard_eq_toFinset_card _ D.crossings_finite] using h.symm

end Paper170

end
end

section

noncomputable section
namespace Paper170

theorem complete_graph_upper_drawing (n : ℕ) :
    ∃ D : AdmissibleDrawing (completeGraph n), crossingCount D = (crossingTuples n).card := by
  obtain ⟨C⟩ := circle_configuration_exists n
  obtain ⟨D, hD⟩ := two_page_drawing_exists C
  exact ⟨D, two_page_crossing_count C D hD⟩

end Paper170

end
end

end OAI
