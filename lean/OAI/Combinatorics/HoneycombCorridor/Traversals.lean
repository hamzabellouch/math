import Mathlib
import OAI.Combinatorics.HoneycombCorridor.CollisionCancellation

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem outgoingSlot_injective (g : Germ) : Function.Injective (outgoingSlot g) := by
  intro b c h
  rcases g with ⟨v,k⟩
  fin_cases k <;> cases b <;> cases c <;> simp [outgoingSlot] at h ⊢

theorem local_contour_support (q : EdgeIndex →₀ ℤ) (g : Germ) (b : Bool)
    (hq : LocalContour q g b) (k : Fin 3) :
    edgeOf (g.1,k) ∈ q.support ↔ k = g.2 ∨ k = outgoingSlot g b := by
  rw [Finsupp.mem_support_iff]
  change (¬ q (edgeOf (g.1,k)) = 0) ↔ _
  rw [← orientedFlow_zero_iff q (g.1,k),hq k]
  have hn := outgoingSlot_ne g b
  by_cases hi : k = g.2
  · subst k
    simp [Ne.symm hn]
  · by_cases ho : k = outgoingSlot g b
    · subst k
      simp [hn]
    · simp [hi,ho]

theorem local_contour_unique (q r : EdgeIndex →₀ ℤ) (hs : q.support = r.support)
    (g : Germ) (b c : Bool) (hq : LocalContour q g b) (hr : LocalContour r g c) : b = c := by
  apply outgoingSlot_injective g
  have hm : edgeOf (g.1,outgoingSlot g b) ∈ r.support := by
    rw [← hs]
    exact (local_contour_support q g b hq _).mpr (Or.inr rfl)
  have h := (local_contour_support r g c hr _).mp hm
  exact h.resolve_left (outgoingSlot_ne g b)

theorem stopped_contour_unique (D : Finset Vertex) (g : Germ) (w u : List Bool)
    (q r : EdgeIndex →₀ ℤ) (hs : q.support = r.support)
    (hw : Stopped D g w) (hu : Stopped D g u)
    (hqw : WordContour q g w) (hru : WordContour r g u) : w = u := by
  induction w generalizing D g u with
  | nil =>
      cases u with
      | nil => rfl
      | cons c u => exact (hw hu.1).elim
  | cons b w ih =>
      cases u with
      | nil => exact (hu hw.1).elim
      | cons c u =>
          have he := local_contour_unique q r hs g b c hqw.1 hru.1
          subst c
          exact congrArg (List.cons b) (ih (D.erase g.1) (advance g b) u hw.2 hu.2 hqw.2 hru.2)

theorem closed_stopped (g : Germ) (w : List Bool) (hne : w ≠ [])
    (hN : (traced g w).Nodup) (hc : terminalGerm g w = g) :
    Stopped (traced g w).toFinset g w := by
  apply (stopped_iff_trace _ _ _).mpr
  refine ⟨hN,by simp,Or.inr ?_⟩
  rw [hc]
  obtain ⟨b,u,rfl⟩ := List.exists_cons_of_ne_nil hne
  simp [traced]

theorem closed_traversal_unique (g : Germ) (w u : List Bool)
    (hwne : w ≠ []) (hwN : (traced g w).Nodup) (hwc : terminalGerm g w = g)
    (hune : u ≠ []) (huN : (traced g u).Nodup) (huc : terminalGerm g u = g)
    (hs : (wordFlow g w).support = (wordFlow g u).support) : w = u := by
  have hD : (traced g w).toFinset = (traced g u).toFinset := by
    rw [← wordFlow_edgeVertices g w hwN hwc,← wordFlow_edgeVertices g u huN huc,hs]
  have hu := closed_stopped g u hune huN huc
  rw [← hD] at hu
  exact stopped_contour_unique (traced g w).toFinset g w u _ _ hs
    (closed_stopped g w hwne hwN hwc) hu
    (simple_closed_word_contour g w hwN hwc) (simple_closed_word_contour g u huN huc)

namespace Polygon

def Traverses (P : Polygon) (g : Germ) (w : List Bool) : Prop :=
  w ≠ [] ∧ (traced g w).Nodup ∧ terminalGerm g w = g ∧ (wordFlow g w).support = P.val

theorem traverses_chosen (P : Polygon) : P.Traverses P.germ P.turns := P.traversal

theorem Traverses.vertices {P : Polygon} {g : Germ} {w : List Bool}
    (h : P.Traverses g w) : P.vertices = (traced g w).toFinset := by
  change edgeVertices P.val = _
  rw [← h.2.2.2]
  exact wordFlow_edgeVertices g w h.2.1 h.2.2.1

theorem Traverses.unique {P : Polygon} {g : Germ} {w u : List Bool}
    (h : P.Traverses g w) (h' : P.Traverses g u) : w = u :=
  closed_traversal_unique g w u h.1 h.2.1 h.2.2.1 h'.1 h'.2.1 h'.2.2.1
    (h.2.2.2.trans h'.2.2.2.symm)

theorem Traverses.reverse {P : Polygon} {g : Germ} {b : Bool} {w : List Bool}
    (h : P.Traverses g (b :: w)) :
    P.Traverses (reverseLoopGerm g b) ((!b) :: reverseTurns w) := by
  refine ⟨by simp,reverse_loop_nodup g b w h.2.2.1 h.2.1,
    reverse_loop_terminal g b w h.2.2.1,?_⟩
  rw [reverse_loop_flow g b w h.2.2.1,Finsupp.support_neg,h.2.2.2]

theorem exists_rooted (P : Polygon) (v : Vertex) (hv : v ∈ P.vertices) :
    ∃ (k : Fin 3) (w : List Bool), P.Traverses (v,k) w := by
  rw [P.vertices_traversal,List.mem_toFinset] at hv
  obtain ⟨u,b,t,he,hv⟩ := mem_traced_split P.germ P.turns v hv
  have hN : (traced P.germ (u ++ b :: t)).Nodup := he ▸ P.traversal.2.1
  have hc : terminalGerm P.germ (u ++ b :: t) = P.germ := he ▸ P.traversal.2.2.1
  obtain ⟨hN',hc',hq'⟩ := closed_word_rotate P.germ u (b :: t) hN hc
  have hq : (wordFlow (terminalGerm P.germ u) ((b :: t) ++ u)).support = P.val := by
    rw [hq',← he,P.traversal.2.2.2]
  have ht : terminalGerm P.germ u = (v,(terminalGerm P.germ u).2) := Prod.ext hv rfl
  rw [ht] at hN' hc' hq
  exact ⟨(terminalGerm P.germ u).2,(b :: t) ++ u,by simp,hN',hc',hq⟩

end Polygon

def IsCycleAt (P : Polygon) (v : Vertex) (e : Fin 3 × List Bool) : Prop :=
  P.Traverses (v,e.1) e.2

noncomputable def cyclesAt (P : Polygon) (v : Vertex) : Finset (Fin 3 × List Bool) := by
  classical
  exact (Finset.univ.biUnion fun k : Fin 3 =>
    (leaves P.vertices (v,k)).image fun w => (k,w)).filter (IsCycleAt P v)

@[simp] theorem mem_cyclesAt (P : Polygon) (v : Vertex) (e : Fin 3 × List Bool) :
    e ∈ cyclesAt P v ↔ IsCycleAt P v e := by
  classical
  rw [cyclesAt,Finset.mem_filter]
  constructor
  · exact And.right
  · intro he
    refine ⟨Finset.mem_biUnion.mpr ⟨e.1,Finset.mem_univ _,Finset.mem_image.mpr
      ⟨e.2,?_,rfl⟩⟩,he⟩
    apply (mem_leaves_iff _ _ _).mpr
    rw [he.vertices]
    exact closed_stopped _ _ he.1 he.2.1 he.2.2.1

def reverseCycle (v : Vertex) (e : Fin 3 × List Bool) : Fin 3 × List Bool :=
  match e.2 with
  | [] => e
  | b :: w => (outgoingSlot (v,e.1) b,(!b) :: reverseTurns w)

theorem cycle_reverse_mem (P : Polygon) (v : Vertex) (e : Fin 3 × List Bool)
    (he : e ∈ cyclesAt P v) : reverseCycle v e ∈ cyclesAt P v := by
  rw [mem_cyclesAt] at he ⊢
  obtain ⟨b,w,hbw⟩ := List.exists_cons_of_ne_nil he.1
  have hr : P.Traverses (v,e.1) (b :: w) := hbw ▸ he
  have hrev := hr.reverse
  simpa only [IsCycleAt,reverseCycle,hbw,reverseLoopGerm] using hrev

theorem cyclesAt_eq_pair (P : Polygon) (v : Vertex) (e : Fin 3 × List Bool)
    (he : e ∈ cyclesAt P v) : cyclesAt P v = {e,reverseCycle v e} := by
  classical
  have htr := (mem_cyclesAt P v e).mp he
  obtain ⟨b,w,hbw⟩ := List.exists_cons_of_ne_nil htr.1
  have hw : P.Traverses (v,e.1) (b :: w) := hbw ▸ htr
  have hr := hw.reverse
  ext f
  constructor
  · intro hf
    have hftr := (mem_cyclesAt P v f).mp hf
    obtain ⟨c,u,hcu⟩ := List.exists_cons_of_ne_nil hftr.1
    have hf' : P.Traverses (v,f.1) (c :: u) := hcu ▸ hftr
    have hm : edgeOf (v,f.1) ∈ (wordFlow (v,e.1) (b :: w)).support := by
      rw [hw.2.2.2,← hf'.2.2.2]
      apply (local_contour_support _ (v,f.1) c
        (simple_closed_word_contour _ _ hf'.2.1 hf'.2.2.1).1 _).mpr
      exact Or.inl rfl
    have hslots := (local_contour_support _ (v,e.1) b
      (simple_closed_word_contour _ _ hw.2.1 hw.2.2.1).1 f.1).mp hm
    simp only [Finset.mem_insert,Finset.mem_singleton]
    rcases hslots with hs | hs
    · left
      apply Prod.ext hs
      have hst : P.Traverses (v,e.1) f.2 := by
        simpa only [IsCycleAt,hs] using hftr
      exact hst.unique htr
    · right
      have hst : P.Traverses (reverseLoopGerm (v,e.1) b) f.2 := by
        simpa only [IsCycleAt,hs,reverseLoopGerm] using hftr
      have heq := hst.unique hr
      apply Prod.ext
      · simpa only [reverseCycle,hbw] using hs
      · simpa only [reverseCycle,hbw] using heq
  · intro hf
    simp only [Finset.mem_insert,Finset.mem_singleton] at hf
    rcases hf with rfl | rfl
    · exact he
    · exact cycle_reverse_mem P v e he

theorem reverseCycle_ne (P : Polygon) (v : Vertex) (e : Fin 3 × List Bool)
    (he : e ∈ cyclesAt P v) : reverseCycle v e ≠ e := by
  obtain ⟨b,w,hbw⟩ := List.exists_cons_of_ne_nil ((mem_cyclesAt P v e).mp he).1
  intro hh
  have hs := congrArg Prod.fst hh
  simp only [reverseCycle,hbw] at hs
  exact outgoingSlot_ne (v,e.1) b hs

end PolynomialVacuumBridge.Corridor

end

end OAI
