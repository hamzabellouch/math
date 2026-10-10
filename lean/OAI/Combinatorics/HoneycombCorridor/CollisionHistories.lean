import Mathlib
import OAI.Combinatorics.HoneycombCorridor.CycleSplice

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

@[simp] theorem neighbor_ne_self (v : Vertex) (k : Fin 3) : neighbor v k ≠ v := by
  cases v <;> fin_cases k <;> simp [neighbor]

@[simp] theorem outgoingSlot_ne (g : Germ) (b : Bool) : outgoingSlot g b ≠ g.2 := by
  rcases g with ⟨v,k⟩
  fin_cases k <;> cases b <;> simp [outgoingSlot]

theorem terminal_previous_mem (g : Germ) (w : List Bool) (hw : w ≠ []) :
    (reverseGerm (terminalGerm g w)).1 ∈ traced g w := by
  induction w generalizing g with
  | nil => contradiction
  | cons b w ih =>
      cases w with
      | nil => simp [terminalGerm,reverseGerm,advance,traced]
      | cons c w =>
          exact List.mem_cons_of_mem _ (ih (advance g b) (by simp))

theorem terminal_previous_suffix (g : Germ) (b : Bool) (w : List Bool) (hw : w ≠ []) :
    (reverseGerm (terminalGerm g (b :: w))).1 ∈ traced (advance g b) w :=
  terminal_previous_mem (advance g b) w hw

theorem return_slot_ne_outgoing (g : Germ) (b : Bool) (w : List Bool)
    (hN : (traced g (b :: w)).Nodup)
    (hc : (terminalGerm g (b :: w)).1 = g.1) :
    (terminalGerm g (b :: w)).2 ≠ outgoingSlot g b := by
  cases w with
  | nil =>
      have h : neighbor g.1 (outgoingSlot g b) = g.1 := hc
      exact (neighbor_ne_self _ _ h).elim
  | cons c w =>
      intro hs
      cases w with
      | nil =>
          exact outgoingSlot_ne (advance g b) c hs
      | cons d w =>
          have hm := terminal_previous_mem (advance (advance g b) c) (d :: w) (by simp)
          have he : (reverseGerm (terminalGerm (advance (advance g b) c) (d :: w))).1 =
              (advance g b).1 := by
            change neighbor (terminalGerm g (b :: c :: d :: w)).1
              (terminalGerm g (b :: c :: d :: w)).2 = _
            rw [hc,hs]
            rfl
          rw [he] at hm
          exact (List.nodup_cons.mp (List.nodup_cons.mp hN).2).1 hm

theorem return_slot_ne_incoming (g : Germ) (w : List Bool) (hw : w ≠ [])
    (hc : (terminalGerm g w).1 = g.1)
    (hback : (reverseGerm g).1 ∉ traced g w) :
    (terminalGerm g w).2 ≠ g.2 := by
  intro hs
  have hm := terminal_previous_mem g w hw
  have he : reverseGerm (terminalGerm g w) = reverseGerm g := by
    congr 1
    exact Prod.ext hc hs
  rw [he] at hm
  exact hback hm

theorem collision_root_slots (g : Germ) (b : Bool) (w : List Bool)
    (hN : (traced g (b :: w)).Nodup)
    (hc : (terminalGerm g (b :: w)).1 = g.1)
    (hback : (reverseGerm g).1 ∉ traced g (b :: w)) :
    stemGerm (terminalGerm g (b :: w)) (!b) = g ∧
    advance (terminalGerm g (b :: w)) (!b) = advance g b := by
  have h1 := return_slot_ne_outgoing g b w hN hc
  have h2 := return_slot_ne_incoming g (b :: w) (by simp) hc hback
  let t := terminalGerm g (b :: w)
  have ht : t.1 = g.1 := hc
  change stemGerm t (!b) = g ∧ advance t (!b) = advance g b
  change t.2 ≠ outgoingSlot g b at h1
  change t.2 ≠ g.2 at h2
  rcases g with ⟨v,k⟩
  rcases t with ⟨v',l⟩
  simp only at ht
  subst v'
  fin_cases k <;> fin_cases l <;> cases b <;>
    simp [outgoingSlot] at h1 h2 ⊢ <;>
    simp [stemGerm,unusedSlot,advance,outgoingSlot]

def reverseAt (g : Germ) (v : Vertex) : List Bool → List Bool
  | [] => []
  | b :: w => if g.1 = v then (!b) :: reverseTurns w
    else b :: reverseAt (advance g b) v w

@[simp] theorem reverseAt_involutive (g : Germ) (v : Vertex) (w : List Bool) :
    reverseAt g v (reverseAt g v w) = w := by
  induction w generalizing g with
  | nil => rfl
  | cons b w ih =>
      by_cases h : g.1 = v
      · simp [reverseAt,h]
      · simp [reverseAt,h,ih]

@[simp] theorem reverseAt_length (g : Germ) (v : Vertex) (w : List Bool) :
    (reverseAt g v w).length = w.length := by
  induction w generalizing g with
  | nil => rfl
  | cons b w ih =>
      by_cases h : g.1 = v <;> simp [reverseAt,h,reverseTurns,ih]

theorem stopped_iff_trace (D : Finset Vertex) (g : Germ) (w : List Bool) :
    Stopped D g w ↔ (traced g w).Nodup ∧ (∀ v ∈ traced g w, v ∈ D) ∧
      ((terminalGerm g w).1 ∉ D ∨ (terminalGerm g w).1 ∈ traced g w) := by
  induction w generalizing D g with
  | nil => simp [Stopped,traced,terminalGerm]
  | cons b w ih =>
      simp only [Stopped,ih,traced,List.nodup_cons,List.mem_cons,terminalGerm]
      constructor
      · rintro ⟨hg,hN,hD,ht⟩
        refine ⟨⟨?_,hN⟩,?_,?_⟩
        · intro hm
          exact (Finset.mem_erase.mp (hD _ hm)).1 rfl
        · intro v hv
          rcases hv with rfl | hv
          · exact hg
          · exact Finset.mem_of_mem_erase (hD _ hv)
        · rcases ht with ht | ht
          · by_cases hm : (terminalGerm (advance g b) w).1 ∈ D
            · right; left
              by_contra hn
              exact ht (Finset.mem_erase.mpr ⟨hn,hm⟩)
            · exact Or.inl hm
          · exact Or.inr (Or.inr ht)
      · rintro ⟨⟨hn,hN⟩,hD,ht⟩
        refine ⟨hD _ (Or.inl rfl),hN,?_,?_⟩
        · intro v hv
          exact Finset.mem_erase.mpr ⟨fun he => hn (he ▸ hv),hD _ (Or.inr hv)⟩
        · rcases ht with ht | ht | ht
          · exact Or.inl (fun h => ht (Finset.mem_of_mem_erase h))
          · exact Or.inl (by simp [ht])
          · exact Or.inr ht

theorem reverse_return_trace (g : Germ) (b : Bool) (w : List Bool)
    (hN : (traced g (b :: w)).Nodup)
    (hc : (terminalGerm g (b :: w)).1 = g.1)
    (hback : (reverseGerm g).1 ∉ traced g (b :: w)) :
    traced g ((!b) :: reverseTurns w) =
      g.1 :: (traced (advance g b) w).reverse ∧
    (terminalGerm g ((!b) :: reverseTurns w)).1 = g.1 := by
  let t := terminalGerm g (b :: w)
  obtain ⟨hs,ha⟩ := collision_root_slots g b w hN hc hback
  have ht : terminalGerm t ((!b) :: w) = t := by
    change terminalGerm (advance t (!b)) w = t
    rw [ha]
    rfl
  have hr := stem_reverse_trace t (!b) w ht
  have he := reverse_loop_terminal t (!b) w ht
  simp only [Bool.not_not] at hr he
  rw [hs,ha,hc] at hr
  constructor
  · exact hr
  · have hrev : advance g (!b) = advance (reverseLoopGerm t (!b)) b := by
      have h1 := stem_reverse t (!b)
      rw [hs] at h1
      exact h1.trans (by simpa using (reverseLoop_advance t (!b)).symm)
    change (terminalGerm (advance g (!b)) (reverseTurns w)).1 = _
    rw [hrev]
    change (terminalGerm (reverseLoopGerm t (!b)) (b :: reverseTurns w)).1 = _
    rw [he]
    exact hc

@[simp] theorem reverse_advance_vertex (g : Germ) (b : Bool) :
    (reverseGerm (advance g b)).1 = g.1 := by
  simp [reverseGerm, advance]

theorem reverseAt_collision (g : Germ) (v : Vertex) (w : List Bool)
    (hN : (traced g w).Nodup) (hv : v ∈ traced g w)
    (ht : (terminalGerm g w).1 = v)
    (hback : (reverseGerm g).1 ∉ traced g w) :
    (traced g (reverseAt g v w)).Perm (traced g w) ∧
    (terminalGerm g (reverseAt g v w)).1 = v := by
  induction w generalizing g with
  | nil => simp [traced] at hv
  | cons b w ih =>
      by_cases hg : g.1 = v
      · have hc : (terminalGerm g (b :: w)).1 = g.1 := ht.trans hg.symm
        obtain ⟨hr,he⟩ := reverse_return_trace g b w hN hc hback
        simp only [reverseAt,ite_eq_left hg]
        rw [hr]
        exact ⟨List.Perm.cons _ (List.reverse_perm _),he.trans hg⟩
      · have hnt := (List.nodup_cons.mp hN)
        have hvt : v ∈ traced (advance g b) w := by
          simpa only [traced,List.mem_cons,eq_comm (a := v),hg,false_or] using hv
        have hbt : (reverseGerm (advance g b)).1 ∉ traced (advance g b) w := by
          simpa only [reverse_advance_vertex] using hnt.1
        obtain ⟨hp,he⟩ := ih (advance g b) hnt.2 hvt ht hbt
        simp only [reverseAt,ite_eq_right hg,traced,terminalGerm]
        exact ⟨List.Perm.cons _ hp,he⟩

def collisionReverse (g : Germ) (w : List Bool) : List Bool :=
  reverseAt g (terminalGerm g w).1 w

theorem collisionReverse_properties (g : Germ) (w : List Bool)
    (hN : (traced g w).Nodup) (ht : (terminalGerm g w).1 ∈ traced g w)
    (hback : (reverseGerm g).1 ∉ traced g w) :
    (traced g (collisionReverse g w)).Perm (traced g w) ∧
    (terminalGerm g (collisionReverse g w)).1 = (terminalGerm g w).1 ∧
    collisionReverse g (collisionReverse g w) = w := by
  obtain ⟨hp,he⟩ := reverseAt_collision g (terminalGerm g w).1 w hN ht rfl hback
  refine ⟨hp,he,?_⟩
  unfold collisionReverse
  rw [he]
  exact reverseAt_involutive _ _ _

theorem collisionReverse_leaf (D : Finset Vertex) (g : Germ) (w : List Bool)
    (hw : w ∈ leaves D g) (hg : (reverseGerm g).1 ∉ D)
    (ht : (terminalGerm g w).1 ∈ D) :
    collisionReverse g w ∈ leaves D g ∧
    (terminalGerm g (collisionReverse g w)).1 ∈ D ∧
    (∀ v, v ∈ traced g (collisionReverse g w) ↔ v ∈ traced g w) ∧
    collisionReverse g (collisionReverse g w) = w := by
  have hs := (stopped_iff_trace D g w).mp ((mem_leaves_iff D g w).mp hw)
  have hm : (terminalGerm g w).1 ∈ traced g w := hs.2.2.resolve_left (not_not.mpr ht)
  have hb : (reverseGerm g).1 ∉ traced g w := fun h => hg (hs.2.1 _ h)
  obtain ⟨hp,he,hinv⟩ := collisionReverse_properties g w hs.1 hm hb
  refine ⟨(mem_leaves_iff _ _ _).mpr ((stopped_iff_trace _ _ _).mpr ?_),he ▸ ht,
    fun v => hp.mem_iff,hinv⟩
  refine ⟨hp.nodup_iff.mpr hs.1,?_,Or.inr ?_⟩
  · intro v hv
    exact hs.2.1 v (hp.mem_iff.mp hv)
  · rw [he]
    exact hp.mem_iff.mpr hm

end PolynomialVacuumBridge.Corridor

end

end OAI
