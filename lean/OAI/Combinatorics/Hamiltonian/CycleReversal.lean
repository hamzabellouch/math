import OAI.Combinatorics.Hamiltonian.ColoredDual

namespace OAI

/-! Reversal involutions on partners of a fixed incidence state. -/

namespace Barnette

open Fin.NatCast

variable {V : Type*} {G : SimpleGraph V}

theorem cycleCoordinates_of_not_acyclic (hG : ¬G.IsAcyclic) :
    Nonempty (CycleCoordinates G) := by
  classical
  simp only [SimpleGraph.IsAcyclic, not_forall, not_not] at hG
  obtain ⟨v, p, hp⟩ := hG
  have hlen : 3 ≤ p.length := hp.isCircuit.three_le_length
  obtain ⟨f⟩ := (SimpleGraph.cycleGraph_isContained_iff (show 2 < p.length by omega)).mpr
    ⟨v, p, hp, rfl⟩
  have heq : p.length = (p.length - 3) + 3 := by omega
  rw [heq] at f
  refine ⟨⟨p.length - 3, ⟨f.toHom, f.injective⟩, ?_⟩⟩
  intro i
  apply f.toHom.map_adj
  apply SimpleGraph.cycleGraph_adj'.mpr
  right
  simp

namespace TriangleSystem

variable {A : Type*} (T : TriangleSystem A V) {X : Set V}

theorem opposite_indices : ∀ i j k l s : Fin 3,
    i ≠ j → k ≠ l → i ≠ s → j ≠ s → k ≠ s → l ≠ s →
    (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by decide

structure OppositeCycle (s : T.State X) where
  cycle : CycleCoordinates (T.oppositeGraph s)
  face : Fin (cycle.n + 3) ↪ A
  leftCorner : Fin (cycle.n + 3) → Fin 3
  rightCorner : Fin (cycle.n + 3) → Fin 3
  left_eq : ∀ i, T.vertex (face i) (leftCorner i) = cycle.vertex i
  right_eq : ∀ i, T.vertex (face i) (rightCorner i) = cycle.vertex (i + 1)
  left_ne : ∀ i, leftCorner i ≠ s.val (face i)
  right_ne : ∀ i, rightCorner i ≠ s.val (face i)

theorem oppositeCycle_nonempty (s : T.State X) (hc : ¬(T.oppositeGraph s).IsAcyclic) :
    Nonempty (T.OppositeCycle s) := by
  classical
  obtain ⟨C⟩ := cycleCoordinates_of_not_acyclic hc
  choose face l r hl hr hls hrs using fun i => (C.adjacent i).2
  have hlr (i) : l i ≠ r i := by
    intro h
    have hh : C.vertex i = C.vertex (i + 1) := (hl i).symm.trans (h ▸ hr i)
    have heq := C.vertex.injective hh
    apply cyclic_one_ne_zero C.n
    exact add_left_cancel (by simpa using heq.symm : i + 1 = i + 0)
  have hface : Function.Injective face := by
    intro i j hij
    have hls' := hls j
    have hrs' := hrs j
    rw [← hij] at hls' hrs'
    have h := opposite_indices (l i) (r i) (l j) (r j) (s.val (face i))
      (hlr i) (hlr j) (hls i) (hrs i) hls' hrs'
    apply C.edge_indices_unique i j
    rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · left
      exact ⟨(hl i).symm.trans (by rw [hij, h₁, hl]),
        (hr i).symm.trans (by rw [hij, h₂, hr])⟩
    · right
      exact ⟨(hl i).symm.trans (by rw [hij, h₁, hr]),
        (hr i).symm.trans (by rw [hij, h₂, hl])⟩
  exact ⟨⟨C, ⟨face, hface⟩, l, r, hl, hr, hls, hrs⟩⟩

namespace OppositeCycle

variable {T} {s r : T.State X} (C : T.OppositeCycle s)

theorem corner_ne (i : Fin (C.cycle.n + 3)) : C.leftCorner i ≠ C.rightCorner i := by
  intro h
  have heq : C.cycle.vertex i = C.cycle.vertex (i + 1) :=
    (C.left_eq i).symm.trans (h ▸ C.right_eq i)
  apply cyclic_one_ne_zero C.cycle.n
  exact add_left_cancel (by simpa using (C.cycle.vertex.injective heq).symm : i + 1 = i + 0)

theorem partner_endpoints (hrs : T.Partner r s) (i : Fin (C.cycle.n + 3)) :
    (r.value (C.face i) = C.cycle.vertex i ∧
      T.vertex (C.face i) (thirdIndex (r.val (C.face i)) (s.val (C.face i))) =
        C.cycle.vertex (i + 1)) ∨
    (r.value (C.face i) = C.cycle.vertex (i + 1) ∧
      T.vertex (C.face i) (thirdIndex (r.val (C.face i)) (s.val (C.face i))) =
        C.cycle.vertex i) := by
  have hne : r.val (C.face i) ≠ s.val (C.face i) :=
    fun h => hrs _ ((State.value_eq_iff r s _).mpr h)
  have h := other_corners (C.leftCorner i) (C.rightCorner i)
    (r.val (C.face i)) (s.val (C.face i)) (C.corner_ne i) (C.left_ne i) (C.right_ne i) hne
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · left
    exact ⟨by change T.vertex _ _ = _; rw [← h₁, C.left_eq],
      by rw [← h₂, C.right_eq]⟩
  · right
    exact ⟨by change T.vertex _ _ = _; rw [← h₁, C.right_eq],
      by rw [← h₂, C.left_eq]⟩

theorem partner_orientation (hrs : T.Partner r s) :
    (∀ i, r.value (C.face i) = C.cycle.vertex i) ∨
      (∀ i, r.value (C.face i) = C.cycle.vertex (i + 1)) := by
  apply C.cycle.tail_orientation C.face r.value r.value_injective
  intro i
  exact (C.partner_endpoints hrs i).imp And.left And.left

end OppositeCycle
end TriangleSystem
end Barnette

namespace Barnette.TriangleSystem

open Fin.NatCast

variable {A V : Type*} {T : TriangleSystem A V} {X : Set V} {s : T.State X}

namespace OppositeCycle

variable (C : T.OppositeCycle s)

noncomputable def changedCorners (r : T.State X) (t : A) : Fin 3 := by
  classical
  exact if t ∈ Set.range C.face then thirdIndex (r.val t) (s.val t) else r.val t

@[simp] theorem changedCorners_image (r : T.State X) (i : Fin (C.cycle.n + 3)) :
    C.changedCorners r (C.face i) = thirdIndex (r.val (C.face i)) (s.val (C.face i)) := by
  classical
  simp [changedCorners]

theorem changed_assignment_permutation (r : T.State X) (hrs : T.Partner r s) :
    ∃ e : Equiv.Perm A, ∀ t, T.vertex t (C.changedCorners r t) = r.value (e t) := by
  classical
  let f := Equiv.ofInjective C.face C.face.injective
  rcases C.partner_orientation hrs with hforward | hbackward
  · let e := (Equiv.addRight (1 : Fin (C.cycle.n + 3))).extendDomain f
    refine ⟨e, ?_⟩
    intro t
    by_cases ht : t ∈ Set.range C.face
    · obtain ⟨i, rfl⟩ := ht
      have he : e (C.face i) = C.face (i + 1) := by
        exact (Equiv.Perm.extendDomain_apply_image _ f i)
      rw [C.changedCorners_image, he, hforward]
      rcases C.partner_endpoints hrs i with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · exact ((C.cycle.adjacent i).1 ((hforward i).symm.trans h)).elim
    · rw [changedCorners, ite_eq_right ht, Equiv.Perm.extendDomain_apply_not_subtype _ f ht]
      rfl
  · let e := (Equiv.addRight (-1 : Fin (C.cycle.n + 3))).extendDomain f
    refine ⟨e, ?_⟩
    intro t
    by_cases ht : t ∈ Set.range C.face
    · obtain ⟨i, rfl⟩ := ht
      have he : e (C.face i) = C.face (i - 1) := by
        calc
          e (C.face i) = C.face (i + (-1 : Fin (C.cycle.n + 3))) :=
            Equiv.Perm.extendDomain_apply_image _ f i
          _ = C.face (i - 1) := congrArg C.face (sub_eq_add_neg i 1).symm
      rw [C.changedCorners_image, he, hbackward, sub_add_cancel]
      rcases C.partner_endpoints hrs i with ⟨h, _⟩ | ⟨_, h⟩
      · exact ((C.cycle.adjacent i).1 (h.symm.trans (hbackward i))).elim
      · exact h
    · rw [changedCorners, ite_eq_right ht, Equiv.Perm.extendDomain_apply_not_subtype _ f ht]
      rfl

noncomputable def reverse (r : T.State X) (hrs : T.Partner r s) : T.State X := by
  let e := (C.changed_assignment_permutation r hrs).choose
  have he : ∀ t, T.vertex t (C.changedCorners r t) = r.value (e t) :=
    (C.changed_assignment_permutation r hrs).choose_spec
  refine ⟨C.changedCorners r, ?_, ?_⟩
  · intro t u h
    change T.vertex t (C.changedCorners r t) = T.vertex u (C.changedCorners r u) at h
    rw [he t, he u] at h
    exact e.injective (r.value_injective h)
  · calc
      Set.range (fun t => T.vertex t (C.changedCorners r t)) = Set.range r.value := by
        ext v
        constructor
        · rintro ⟨t, rfl⟩
          exact ⟨e t, (he t).symm⟩
        · rintro ⟨u, rfl⟩
          refine ⟨e.symm u, ?_⟩
          change T.vertex (e.symm u) (C.changedCorners r (e.symm u)) = r.value u
          rw [he, e.apply_symm_apply]
      _ = X := r.value_range

@[simp] theorem reverse_val (r : T.State X) (hrs : T.Partner r s) :
    (C.reverse r hrs).val = C.changedCorners r := rfl

theorem reverse_partner (r : T.State X) (hrs : T.Partner r s) :
    T.Partner (C.reverse r hrs) s := by
  classical
  intro t h
  have hi : C.changedCorners r t = s.val t :=
    T.vertex_injective t h
  by_cases ht : t ∈ Set.range C.face
  · rw [changedCorners, ite_eq_left ht] at hi
    have hne : r.val t ≠ s.val t := fun h => hrs t ((State.value_eq_iff r s t).mpr h)
    exact (thirdIndex_distinct _ _ hne).2 hi
  · rw [changedCorners, ite_eq_right ht] at hi
    exact hrs t ((State.value_eq_iff r s t).mpr hi)

@[simp] theorem reverse_reverse (r : T.State X) (hrs : T.Partner r s) :
    C.reverse (C.reverse r hrs) (C.reverse_partner r hrs) = r := by
  classical
  apply Subtype.ext
  funext t
  change C.changedCorners (C.reverse r hrs) t = r.val t
  by_cases ht : t ∈ Set.range C.face
  · simp only [changedCorners, ht, ite_true, reverse_val, thirdIndex_involution]
  · simp only [changedCorners, ht, ite_false, reverse_val]

theorem reverse_ne (r : T.State X) (hrs : T.Partner r s) : C.reverse r hrs ≠ r := by
  intro h
  have heq := congrFun (congrArg Subtype.val h) (C.face 0)
  change C.changedCorners r (C.face 0) = r.val (C.face 0) at heq
  rw [C.changedCorners_image] at heq
  have hne : r.val (C.face 0) ≠ s.val (C.face 0) :=
    fun h => hrs _ ((State.value_eq_iff r s _).mpr h)
  exact (thirdIndex_distinct _ _ hne).1 heq

end OppositeCycle

def Partners (s : T.State X) := {r : T.State X // T.Partner r s}

namespace OppositeCycle

variable (C : T.OppositeCycle s)

noncomputable def reversal (r : T.Partners s) : T.Partners s :=
  ⟨C.reverse r.val r.property, C.reverse_partner r.val r.property⟩

theorem reversal_involutive : Function.Involutive C.reversal := by
  intro r
  apply Subtype.ext
  exact C.reverse_reverse r.val r.property

theorem reversal_ne (r : T.Partners s) : C.reversal r ≠ r := by
  intro h
  exact C.reverse_ne r.val r.property (congrArg Subtype.val h)

end OppositeCycle
end Barnette.TriangleSystem

end OAI
