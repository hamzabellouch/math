import Mathlib
import OAI.Combinatorics.HoneycombCorridor.ReturnCycles
import OAI.Combinatorics.HoneycombCorridor.PolygonNesting

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

def stemEnd (v : Vertex) (s : RayRecord) : Germ := terminalGerm (rayGerm v s.1) s.2

def IsPolygonStem (D : Finset Vertex) (v : Vertex) (P : Polygon) (s : RayRecord) : Prop :=
  v ∉ P.vertices ∧ Stopped ((D \ P.vertices).erase v) (rayGerm v s.1) s.2 ∧
    (stemEnd v s).1 ∈ P.vertices

noncomputable def polygonStems (D : Finset Vertex) (v : Vertex) (P : Polygon) :
    Finset RayRecord := by
  classical
  exact (rayLeaves (D \ P.vertices) v).filter (IsPolygonStem D v P)

@[simp] theorem mem_polygonStems (D : Finset Vertex) (v : Vertex) (P : Polygon) (s : RayRecord) :
    s ∈ polygonStems D v P ↔ IsPolygonStem D v P s := by
  classical
  simp only [polygonStems,Finset.mem_filter,mem_rayLeaves]
  exact ⟨And.right,fun h => ⟨h.2.1,h⟩⟩

theorem IsPolygonStem.trace_disjoint {D : Finset Vertex} {v : Vertex} {P : Polygon}
    {s : RayRecord} (hs : IsPolygonStem D v P s) :
    ∀ a ∈ traced (rayGerm v s.1) s.2, a ∉ P.vertices := by
  intro a ha
  exact (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase
    (((stopped_iff_trace _ _ _).mp hs.2.1).2.1 a ha))).2

theorem IsPolygonStem.back_outside {D : Finset Vertex} {v : Vertex} {P : Polygon}
    {s : RayRecord} (hs : IsPolygonStem D v P s) :
    (reverseGerm (stemEnd v s)).1 ∉ P.vertices := by
  by_cases hn : s.2 = []
  · simpa only [stemEnd,hn,terminalGerm,rayGerm,reverseGerm,neighbor_neighbor] using hs.1
  · exact hs.trace_disjoint _ (terminal_previous_mem _ _ hn)

theorem Polygon.neighbor_mem_of_edge (P : Polygon) (g : Germ)
    (hg : edgeOf g ∈ P.val) : (reverseGerm g).1 ∈ P.vertices := by
  apply (mem_edgeVertices P.val _).mpr
  exact ⟨g.2,by change edgeOf (reverseGerm g) ∈ P.val; simpa using hg⟩

theorem thirdSlot_unique (g : Germ) (b : Bool) (k : Fin 3)
    (hi : k ≠ g.2) (ho : k ≠ outgoingSlot g b) : k = unusedSlot g b := by
  rcases g with ⟨v,l⟩
  fin_cases k <;> fin_cases l <;> cases b <;>
    simp [outgoingSlot,unusedSlot] at hi ho ⊢

theorem stemGerm_eq_of_back_outside (P : Polygon) (t : Germ) (k : Fin 3)
    (b : Bool) (w : List Bool) (hc : P.Traverses (t.1,k) (b :: w))
    (hb : (reverseGerm t).1 ∉ P.vertices) : stemGerm (t.1,k) b = t := by
  have hn : edgeOf t ∉ P.val := fun h => hb (P.neighbor_mem_of_edge t h)
  have hloc := (simple_closed_word_contour _ _ hc.2.1 hc.2.2.1).1
  have hslots : ¬ (t.2 = k ∨ t.2 = outgoingSlot (t.1,k) b) := by
    intro hh
    apply hn
    rw [← hc.2.2.2]
    exact (local_contour_support _ (t.1,k) b hloc t.2).mpr hh
  have h := thirdSlot_unique (t.1,k) b t.2
    (fun he => hslots (Or.inl he)) (fun he => hslots (Or.inr he))
  exact Prod.ext rfl h.symm

def attachWord (c : RayRecord) : List Bool :=
  match c.2 with
  | [] => []
  | b :: w => (!b) :: w

theorem attachWord_injective_on_words (c d : RayRecord) (h : attachWord c = attachWord d) :
    c.2 = d.2 := by
  cases hc : c.2 with
  | nil => cases hd : d.2 <;> simp_all [attachWord]
  | cons b w =>
      cases hd : d.2 with
      | nil => simp_all [attachWord]
      | cons e u =>
          have hp : (!b) = (!e) ∧ w = u := by simpa only [attachWord,hc,hd,List.cons.injEq] using h
          have hbe : b = e := by simpa using congrArg Bool.not hp.1
          simp only [hbe,hp.2]

theorem attached_trace (P : Polygon) (t : Germ) (c : RayRecord)
    (hc : c ∈ cyclesAt P t.1) (hb : (reverseGerm t).1 ∉ P.vertices) :
    traced t (attachWord c) = traced (t.1,c.1) c.2 ∧
    terminalGerm t (attachWord c) = (t.1,c.1) := by
  have h := (mem_cyclesAt P t.1 c).mp hc
  obtain ⟨b,w,hw⟩ := List.exists_cons_of_ne_nil h.1
  have htr : P.Traverses (t.1,c.1) (b :: w) := hw ▸ h
  have he := stemGerm_eq_of_back_outside P t c.1 b w htr hb
  simp only [attachWord,hw]
  constructor
  · rw [← he,stem_forward_trace]
    rfl
  · rw [← he,stem_forward_terminal]
    exact htr.2.2.1

theorem first_cut_unique (g : Germ) (a : Vertex) (u r u' r' : List Bool)
    (he : u ++ r = u' ++ r')
    (hu : (terminalGerm g u).1 = a) (hu' : (terminalGerm g u').1 = a)
    (hn : a ∉ traced g u) (hn' : a ∉ traced g u') : u = u' := by
  induction u generalizing g u' with
  | nil =>
      cases u' with
      | nil => rfl
      | cons b u' => exact (hn' (by simp [traced,← hu,terminalGerm])).elim
  | cons b u ih =>
      cases u' with
      | nil => exact (hn (by simp [traced,← hu',terminalGerm])).elim
      | cons c u' =>
          simp only [List.cons_append,List.cons.injEq] at he
          rcases he with ⟨rfl,he⟩
          apply congrArg (List.cons b)
          exact ih (advance g b) u' he hu hu'
            (fun h => hn (List.mem_cons_of_mem _ h))
            (fun h => hn' (List.mem_cons_of_mem _ h))

def spliceRecord (v : Vertex) (s c : RayRecord) : RayRecord :=
  ((rayGerm v s.1).2,s.2 ++ attachWord c)

noncomputable def rayCollisions (D : Finset Vertex) (v : Vertex) : Finset RayRecord := by
  classical
  exact (rayLeaves D v).filter fun e => (stemEnd v e).1 ∈ D.erase v

@[simp] theorem mem_rayCollisions (D : Finset Vertex) (v : Vertex) (e : RayRecord) :
    e ∈ rayCollisions D v ↔ Stopped (D.erase v) (rayGerm v e.1) e.2 ∧
      (stemEnd v e).1 ∈ D.erase v := by
  classical
  simp [rayCollisions]

theorem spliceRecord_mem (D : Finset Vertex) (v : Vertex) (P : Polygon)
    (hP : P ∈ polygons D) (s : RayRecord) (hs : s ∈ polygonStems D v P)
    (c : RayRecord) (hc : c ∈ cyclesAt P (stemEnd v s).1) :
    spliceRecord v s c ∈ rayCollisions D v := by
  have hs := (mem_polygonStems D v P s).mp hs
  have htr := (mem_cyclesAt P _ c).mp hc
  have hat := attached_trace P (stemEnd v s) c hc hs.back_outside
  have hN := (stopped_iff_trace _ _ _).mp hs.2.1
  have hct : (stemEnd v (spliceRecord v s c)).1 = (stemEnd v s).1 := by
    simp only [stemEnd,spliceRecord,terminalGerm_append]
    have hh := congrArg (fun g : Germ => g.1) hat.2
    exact hh
  have htmem : (stemEnd v s).1 ∈ D.erase v :=
    Finset.mem_erase.mpr ⟨fun h => hs.1 (h ▸ hs.2.2),(mem_polygons D P).mp hP hs.2.2⟩
  rw [mem_rayCollisions]
  refine ⟨?_,by rw [hct]; exact htmem⟩
  apply (stopped_iff_trace _ _ _).mpr
  have htrace : traced (rayGerm v (spliceRecord v s c).1) (spliceRecord v s c).2 =
      traced (rayGerm v s.1) s.2 ++ traced ((stemEnd v s).1,c.1) c.2 := by
    change traced (rayGerm v s.1) (s.2 ++ attachWord c) = _
    rw [traced_append]
    change traced (rayGerm v s.1) s.2 ++ traced (stemEnd v s) (attachWord c) = _
    rw [hat.1]
  rw [htrace]
  refine ⟨List.nodup_append.mpr ⟨hN.1,htr.2.1,?_⟩,?_,Or.inr ?_⟩
  · intro a ha b hb hab
    subst b
    exact hs.trace_disjoint a ha (by rw [htr.vertices]; exact List.mem_toFinset.mpr hb)
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp (hN.2.1 a ha)).1,
        (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase (hN.2.1 a ha))).1⟩
    · have haP : a ∈ P.vertices := by rw [htr.vertices]; exact List.mem_toFinset.mpr ha
      exact Finset.mem_erase.mpr ⟨fun h => hs.1 (h ▸ haP),(mem_polygons D P).mp hP haP⟩
  · change (stemEnd v (spliceRecord v s c)).1 ∈ _
    rw [hct]
    apply List.mem_append_right
    obtain ⟨b,w,hw⟩ := List.exists_cons_of_ne_nil htr.1
    simp [hw,traced]

end PolynomialVacuumBridge.Corridor

end

end OAI
