import Mathlib
import OAI.Combinatorics.HoneycombCorridor.PolygonSize

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

abbrev RayRecord := Fin 3 × List Bool

def rayGerm (v : Vertex) (k : Fin 3) : Germ := (neighbor v k,k)

noncomputable def rayLeaves (D : Finset Vertex) (v : Vertex) : Finset RayRecord :=
  Finset.univ.biUnion fun k : Fin 3 =>
    (leaves (D.erase v) (rayGerm v k)).image fun w => (k,w)

@[simp] theorem mem_rayLeaves (D : Finset Vertex) (v : Vertex) (e : RayRecord) :
    e ∈ rayLeaves D v ↔ Stopped (D.erase v) (rayGerm v e.1) e.2 := by
  classical
  simp only [rayLeaves,Finset.mem_biUnion,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨k,w,hw,he⟩
    subst e
    exact (mem_leaves_iff _ _ _).mp hw
  · intro h
    exact ⟨e.1,e.2,(mem_leaves_iff _ _ _).mpr h,rfl⟩

noncomputable def rayReturns (D : Finset Vertex) (v : Vertex) : Finset RayRecord := by
  classical
  exact (rayLeaves D v).filter fun e => (terminalGerm (rayGerm v e.1) e.2).1 = v

@[simp] theorem mem_rayReturns (D : Finset Vertex) (v : Vertex) (e : RayRecord) :
    e ∈ rayReturns D v ↔ Stopped (D.erase v) (rayGerm v e.1) e.2 ∧
      (terminalGerm (rayGerm v e.1) e.2).1 = v := by
  classical
  simp [rayReturns]

def omitRoot (v : Vertex) (e : RayRecord) : RayRecord :=
  match e.2 with
  | [] => e
  | b :: w => (outgoingSlot (v,e.1) b,w)

theorem cycle_omitRoot_mem (D : Finset Vertex) (v : Vertex) (P : Polygon)
    (hP : P ∈ polygons D) (e : RayRecord) (he : e ∈ cyclesAt P v) :
    omitRoot v e ∈ rayReturns D v := by
  have h := (mem_cyclesAt P v e).mp he
  obtain ⟨b,w,hw⟩ := List.exists_cons_of_ne_nil h.1
  have htr : P.Traverses (v,e.1) (b :: w) := hw ▸ h
  have hN := List.nodup_cons.mp htr.2.1
  have hd : ∀ u ∈ traced (advance (v,e.1) b) w, u ∈ D.erase v := by
    intro u hu
    refine Finset.mem_erase.mpr ⟨?_,?_⟩
    · intro heq
      subst u
      exact hN.1 hu
    · apply (mem_polygons _ _).mp hP
      rw [htr.vertices]
      simp only [traced,List.mem_toFinset,List.mem_cons]
      exact Or.inr hu
  have hc : (terminalGerm (advance (v,e.1) b) w).1 = v := congrArg Prod.fst htr.2.2.1
  rw [mem_rayReturns]
  simp only [omitRoot,hw]
  change Stopped (D.erase v) (advance (v,e.1) b) w ∧ _
  refine ⟨(stopped_iff_trace _ _ _).mpr ⟨hN.2,hd,Or.inl ?_⟩,hc⟩
  simp [hc]

theorem outgoingSlot_exists (g : Germ) (k : Fin 3) (hk : k ≠ g.2) :
    ∃ b : Bool, outgoingSlot g b = k := by
  rcases g with ⟨v,l⟩
  fin_cases k <;> fin_cases l <;> simp_all [outgoingSlot]

theorem rayReturn_closes (D : Finset Vertex) (v : Vertex) (hv : v ∈ D)
    (e : RayRecord) (he : e ∈ rayReturns D v) :
    ∃ (P : Polygon) (c : RayRecord), P ∈ polygons D ∧ c ∈ cyclesAt P v ∧ omitRoot v c = e := by
  have hs := (mem_rayReturns D v e).mp he
  let g := rayGerm v e.1
  have hne : e.2 ≠ [] := by
    intro hn
    have h := hs.2
    simp only [hn,terminalGerm,rayGerm] at h
    exact neighbor_ne_self _ _ h
  have hstart : g.1 ∈ D.erase v := by
    obtain ⟨b,w,hw⟩ := List.exists_cons_of_ne_nil hne
    exact (show Stopped (D.erase v) g (b :: w) from hw ▸ hs.1).1
  have hexc : IsExcursion (D.erase v) (g,e.2) := by
    refine ⟨hstart,?_,hs.1,?_⟩
    · simp [g,rayGerm,reverseGerm]
    · change (terminalGerm (rayGerm v e.1) e.2).1 ∉ D.erase v
      simp [hs.2]
  let t := terminalGerm g e.2
  have ht : t.1 = v := hs.2
  have hslot : e.1 ≠ t.2 := by
    intro hh
    apply hexc.distinct_ports
    apply Prod.ext
    · change neighbor t.1 t.2 = neighbor v e.1
      rw [ht,hh]
    · exact hh.symm
  obtain ⟨b,hb⟩ := outgoingSlot_exists (v,t.2) e.1 hslot
  have ha : advance (v,t.2) b = g := by
    unfold advance
    rw [hb]
    rfl
  have hfresh := (stopped_iff_trace _ _ _).mp hs.1
  have hN : (traced (v,t.2) (b :: e.2)).Nodup := by
    simp only [traced,ha,List.nodup_cons]
    exact ⟨fun hm => (Finset.mem_erase.mp (hfresh.2.1 v hm)).1 rfl,hfresh.1⟩
  have hc : terminalGerm (v,t.2) (b :: e.2) = (v,t.2) := by
    change terminalGerm (advance (v,t.2) b) e.2 = _
    rw [ha]
    exact Prod.ext ht rfl
  let P := polygonOfClosed (v,t.2) (b :: e.2) (by simp) hN hc
  refine ⟨P,(t.2,b :: e.2),?_,?_,?_⟩
  · apply (mem_polygons D P).mpr
    rw [polygonOfClosed_vertices]
    intro u hu
    simp only [traced,ha,List.mem_toFinset,List.mem_cons] at hu
    rcases hu with rfl | hu
    · exact hv
    · exact Finset.mem_of_mem_erase (hfresh.2.1 u hu)
  · exact (mem_cyclesAt _ _ _).mpr ⟨by simp,hN,hc,rfl⟩
  · simp only [omitRoot,hb]

noncomputable def cyclesIn (D : Finset Vertex) (v : Vertex) : Finset RayRecord :=
  (polygons D).biUnion fun P => cyclesAt P v

theorem cycles_disjoint (v : Vertex) {P Q : Polygon} (hPQ : P ≠ Q) :
    Disjoint (cyclesAt P v) (cyclesAt Q v) := by
  classical
  apply Finset.disjoint_left.mpr
  intro e he hf
  have h := (mem_cyclesAt _ _ _).mp he
  have h' := (mem_cyclesAt _ _ _).mp hf
  exact hPQ (Subtype.ext (h.2.2.2.symm.trans h'.2.2.2))

theorem omitRoot_injOn (D : Finset Vertex) (v : Vertex) :
    Set.InjOn (omitRoot v) (cyclesIn D v) := by
  intro e he f hf hef
  obtain ⟨P,hP,he⟩ := Finset.mem_biUnion.mp he
  obtain ⟨Q,hQ,hf⟩ := Finset.mem_biUnion.mp hf
  have h := (mem_cyclesAt _ _ _).mp he
  have h' := (mem_cyclesAt _ _ _).mp hf
  obtain ⟨b,w,hw⟩ := List.exists_cons_of_ne_nil h.1
  obtain ⟨c,u,hu⟩ := List.exists_cons_of_ne_nil h'.1
  have hp := Prod.mk.inj (show (outgoingSlot (v,e.1) b,w) =
      (outgoingSlot (v,f.1) c,u) from by simpa only [omitRoot,hw,hu] using hef)
  have ha : advance (v,e.1) b = advance (v,f.1) c := by simp only [advance,hp.1]
  have ht : (v,e.1) = (v,f.1) := by
    rw [← h.2.2.1,← h'.2.2.1,hw,hu]
    simp only [terminalGerm,ha,hp.2]
  have hes : e.1 = f.1 := congrArg Prod.snd ht
  have heturn : b = c := outgoingSlot_injective (v,f.1) (by simpa only [hes] using hp.1)
  exact Prod.ext hes (by rw [hw,hu,heturn,hp.2])

theorem return_sum_cycles (D : Finset Vertex) (v : Vertex) (hv : v ∈ D) :
    (∑ e ∈ rayReturns D v, wordWeight e.2) =
      ∑ P ∈ polygons D, ∑ e ∈ cyclesAt P v, wordWeight (omitRoot v e).2 := by
  classical
  have hsum : (∑ e ∈ cyclesIn D v, wordWeight (omitRoot v e).2) =
      ∑ e ∈ rayReturns D v, wordWeight e.2 := by
    apply Finset.sum_bij (fun e _ => omitRoot v e)
    · intro e he
      obtain ⟨P,hP,he⟩ := Finset.mem_biUnion.mp he
      exact cycle_omitRoot_mem D v P hP e he
    · intro e he f hf heq
      exact omitRoot_injOn D v he hf heq
    · intro e he
      obtain ⟨P,c,hP,hc,heq⟩ := rayReturn_closes D v hv e he
      exact ⟨c,Finset.mem_biUnion.mpr ⟨P,hP,hc⟩,heq⟩
    · intro e he
      rfl
  rw [← hsum,cyclesIn,Finset.sum_biUnion]
  intro P hP Q hQ hPQ
  exact cycles_disjoint v hPQ



theorem numeric_faceCount_turn (f : Fin 3 → ℤ) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) (hf : ∀ l, f l = 0 ∨ f l = ε)
    (k : Fin 3) (b : Bool)
    (h : ∀ l : Fin 3, f l - f (l+2) =
      (if l = k + (if b then 2 else 1) then 1 else 0) - (if l = k then 1 else 0)) :
    3 - 2 * (∑ l : Fin 3, if f l ≠ 0 then (1 : ℤ) else 0) = ε * turnUnit b := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have hf0 := hf 0
  have hf1 := hf 1
  have hf2 := hf 2
  clear h hf
  rcases hε with rfl | rfl <;> fin_cases k <;> cases b <;>
    rcases hf0 with hf0 | hf0 <;> rcases hf1 with hf1 | hf1 <;>
    rcases hf2 with hf2 | hf2 <;>
    simp only [Fin.sum_univ_succ] at * <;> simp_all [turnUnit]

theorem contour_faceCount_turn (p : FaceIndex →₀ ℤ) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) (hvals : ∀ a, p a = 0 ∨ p a = ε)
    (q : EdgeIndex →₀ ℤ) (hp : RepresentsFlow p q)
    (g : Germ) (b : Bool) (hw : LocalContour q g b) :
    3 - 2 * faceCount p.support g.1 = ε * turnUnit b := by
  let f : Fin 3 → ℤ := fun l => p (leftFace (g.1,l))
  have hl (l : Fin 3) : f l - f (l+2) =
      (if l = g.2 + (if b then 2 else 1) then 1 else 0) - (if l = g.2 then 1 else 0) := by
    have h := (hp (g.1,l)).symm.trans (hw l)
    simp only [f,rightFace_prev,outgoingSlot] at h ⊢
    exact h
  simpa only [faceCount,Finsupp.mem_support_iff] using
    numeric_faceCount_turn f ε hε (fun l => hvals _) g.2 b hl

theorem Polygon.ccwTurn_traversal (P : Polygon) (g : Germ) (b : Bool) (w : List Bool)
    (h : P.Traverses g (b :: w)) (p : FaceIndex →₀ ℤ) (ε : ℤ)
    (hp : RepresentsFlow p (wordFlow g (b :: w)))
    (hε : ε = 1 ∨ ε = -1) (hvals : ∀ a, p a = 0 ∨ p a = ε) :
    P.ccwTurn g.1 = Real.pi / 3 * (ε * turnUnit b : ℤ) := by
  have ht := contour_faceCount_turn p ε hε hvals _ hp g b
    (simple_closed_word_contour _ _ h.2.1 h.2.2.1).1
  unfold Polygon.ccwTurn
  rw [P.interiorFaces_of_traversal g (b :: w) h.2.1 h.2.2.1 h.2.2.2 p hp]
  congr 1
  exact_mod_cast ht

theorem wordWeight_add_reverse (w : List Bool) :
    wordWeight w + wordWeight (reverseTurns w) =
      (2 : ℂ) * (criticalActivity : ℂ) ^ w.length *
        (Real.cos (Real.pi / 8 * (turnUnits w : ℝ)) : ℂ) := by
  rw [wordWeight_reverse,wordWeight_turnUnits,Complex.exp_ofReal_mul_I]
  simp only [map_mul,map_add,map_pow,Complex.conj_ofReal,Complex.conj_I]
  ring

theorem cycle_return_weight (P : Polygon) (v : Vertex) (e : RayRecord)
    (he : e ∈ cyclesAt P v) :
    wordWeight (omitRoot v e).2 + wordWeight (omitRoot v (reverseCycle v e)).2 =
      (2 : ℂ) * (criticalActivity : ℂ) ^ (P.length - 1) *
        (Real.cos ((3 / 8 : ℝ) * (2 * Real.pi - P.ccwTurn v)) : ℂ) := by
  have h := (mem_cyclesAt P v e).mp he
  obtain ⟨b,w,hw⟩ := List.exists_cons_of_ne_nil h.1
  have htr : P.Traverses (v,e.1) (b :: w) := hw ▸ h
  obtain ⟨p,ε,hp,hpne,hε,hvals⟩ := simple_closed_word_indicator (v,e.1) (b :: w)
    (by simp) htr.2.1 htr.2.2.1
  have ht := simple_polygon_signed_turn (v,e.1) (b :: w) (by simp)
    htr.2.1 htr.2.2.1 p ε hp hpne hε hvals
  have hccw := P.ccwTurn_traversal (v,e.1) b w htr p ε hp hε hvals
  simp only [omitRoot,hw,reverseCycle]
  rw [wordWeight_add_reverse]
  have hlen : P.length - 1 = w.length := by rw [htr.length]; simp
  rw [hlen,hccw]
  congr 2
  have htu : turnUnits w = 6 * ε - turnUnit b := by
    rw [turnUnits_cons] at ht
    rcases hε with he | he <;> rw [he] at ht ⊢ <;> nlinarith
  rw [htu]
  push_cast
  rcases hε with rfl | rfl
  · congr 1
    ring
  · norm_num only [Int.cast_neg,Int.cast_one]
    rw [show Real.pi / 8 * ((-6 : ℝ) - (turnUnit b : ℝ)) =
        -((3 / 8 : ℝ) * (2 * Real.pi - Real.pi / 3 * ((-1 : ℝ) * turnUnit b))) by ring]
    exact Real.cos_neg _

theorem cycle_return_sum (P : Polygon) (v : Vertex) :
    (∑ e ∈ cyclesAt P v, wordWeight (omitRoot v e).2) =
      if v ∈ P.vertices then
        (2 : ℂ) * (criticalActivity : ℂ) ^ (P.length - 1) *
          (Real.cos ((3 / 8 : ℝ) * (2 * Real.pi - P.ccwTurn v)) : ℂ)
      else 0 := by
  classical
  by_cases hv : v ∈ P.vertices
  · obtain ⟨k,w,hw⟩ := P.exists_rooted v hv
    have he := (mem_cyclesAt P v (k,w)).mpr hw
    rw [ite_eq_left hv,cyclesAt_eq_pair P v (k,w) he,Finset.sum_pair
      (Ne.symm (reverseCycle_ne P v (k,w) he))]
    exact cycle_return_weight P v (k,w) he
  · rw [ite_eq_right hv]
    apply Finset.sum_eq_zero
    intro e he
    have h := (mem_cyclesAt P v e).mp he
    obtain ⟨b,w,hw⟩ := List.exists_cons_of_ne_nil h.1
    apply False.elim
    apply hv
    rw [h.vertices,hw]
    simp [traced]

theorem return_sum_polygons (D : Finset Vertex) (v : Vertex) (hv : v ∈ D) :
    (∑ e ∈ rayReturns D v, wordWeight e.2) =
      ∑ P ∈ polygons D, if v ∈ P.vertices then
        (2 : ℂ) * (criticalActivity : ℂ) ^ (P.length - 1) *
          (Real.cos ((3 / 8 : ℝ) * (2 * Real.pi - P.ccwTurn v)) : ℂ)
        else 0 := by
  rw [return_sum_cycles D v hv]
  apply Finset.sum_congr rfl
  intro P hP
  exact cycle_return_sum P v

end PolynomialVacuumBridge.Corridor

end

end OAI
