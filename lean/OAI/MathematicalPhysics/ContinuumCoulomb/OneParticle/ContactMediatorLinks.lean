import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactMediatorGeometry

namespace OAI

/-! The contact adjacency is exactly the edge relation of the actual
nineteen-link gadget, including the signed central attachment. -/

namespace ContinuumCoulomb.ContactMediator
open MediatorIteration

def samePair {α : Type*} (a b c d : α) : Prop :=
  (a = c ∧ b = d) ∨ (a = d ∧ b = c)

theorem samePair_swap_target {α : Type*} {a b c d : α} (h : samePair a b c d) :
    samePair a b d c := h.symm

theorem samePair_trans {α : Type*} {a b c d e f : α}
    (h : samePair a b c d) (k : samePair c d e f) : samePair a b e f := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact k
  · rcases k with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [samePair]

theorem samePair_map {α β : Type*} (f : α → β) {a b c d : α}
    (h : samePair a b c d) : samePair (f a) (f b) (f c) (f d) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [samePair]

def contactPair (negative : Bool) (a : LocalEdge) (x y : ContactGadgetSite) : Prop :=
  samePair (localToContact (localLeft (if negative then 0 else 1) a))
    (localToContact (localRight a)) x y

theorem leftEdge_pair (negative : Bool) (k : Fin 9) :
    contactPair negative (leftEdge k) (Sum.inl k.castSucc) (Sum.inl k.succ) := by
  fin_cases k <;> cases negative <;> norm_num [contactPair, samePair, localToContact, localLeft, localRight,
      leftEdge, rightEdge, secondEndpoint, firstAttachment, localOld, localFirst,
      localSecond, localThird, contactGadgetRightNode, contactGadgetSide]

theorem rightEdge_pair (negative : Bool) (k : Fin 9) :
    contactPair negative (rightEdge k) (contactGadgetRightNode negative k.castSucc)
      (contactGadgetRightNode negative k.succ) := by
  fin_cases k <;> cases negative <;> norm_num [contactPair, samePair, localToContact, localLeft, localRight,
      leftEdge, rightEdge, secondEndpoint, firstAttachment, localOld, localFirst,
      localSecond, localThird, contactGadgetRightNode, contactGadgetSide]

private theorem adjacent_indices {n : ℕ} (i j : Fin (n + 1)) (h : Nat.dist i.val j.val = 1) :
    ∃ k : Fin n, (i = k.castSucc ∧ j = k.succ) ∨ (i = k.succ ∧ j = k.castSucc) := by
  have hi := i.isLt
  have hj := j.isLt
  unfold Nat.dist at h
  by_cases hij : i.val ≤ j.val
  · refine ⟨⟨i.val, by omega⟩, Or.inl ⟨Fin.ext rfl, Fin.ext (by dsimp; omega)⟩⟩
  · refine ⟨⟨j.val, by omega⟩, Or.inr ⟨Fin.ext (by dsimp; omega), Fin.ext rfl⟩⟩

private theorem left_adjacent_exists (negative : Bool) (i j : Fin 10)
    (h : Nat.dist i.val j.val = 1) :
    ∃ a, contactPair negative a (Sum.inl i) (Sum.inl j) := by
  obtain ⟨k, h | h⟩ := adjacent_indices i j h
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨leftEdge k, leftEdge_pair negative k⟩
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨leftEdge k, samePair_swap_target (leftEdge_pair negative k)⟩

private theorem right_nodes (negative : Bool) (k : Fin 8) :
    contactGadgetRightNode negative k.succ.castSucc = Sum.inr (Sum.inl k.castSucc) ∧
    contactGadgetRightNode negative k.succ.succ = Sum.inr (Sum.inl k.succ) := by
  fin_cases k <;> cases negative <;> norm_num [contactPair, samePair, localToContact, localLeft, localRight,
      leftEdge, rightEdge, secondEndpoint, firstAttachment, localOld, localFirst,
      localSecond, localThird, contactGadgetRightNode, contactGadgetSide]

private theorem right_adjacent_exists (negative : Bool) (i j : Fin 9)
    (h : Nat.dist i.val j.val = 1) :
    ∃ a, contactPair negative a (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inl j)) := by
  obtain ⟨k, h | h⟩ := adjacent_indices i j h
  · rcases h with ⟨rfl, rfl⟩
    refine ⟨rightEdge k.succ, ?_⟩
    simpa only [contactPair, (right_nodes negative k).1, (right_nodes negative k).2] using
      rightEdge_pair negative k.succ
  · rcases h with ⟨rfl, rfl⟩
    refine ⟨rightEdge k.succ, ?_⟩
    apply samePair_swap_target
    simpa only [contactPair, (right_nodes negative k).1, (right_nodes negative k).2] using
      rightEdge_pair negative k.succ

theorem contactLinked_exists (negative : Bool) (x y : ContactGadgetSite)
    (h : contactGadgetLinked negative x y) : ∃ a, contactPair negative a x y := by
  rcases x with i | (i | ⟨⟩) <;> rcases y with j | (j | ⟨⟩)
  · exact left_adjacent_exists negative i j h
  · rcases h with ⟨rfl, rfl, rfl⟩
    exact ⟨rightEdge 0, by norm_num [contactPair, samePair, localToContact, localLeft, localRight,
      leftEdge, rightEdge, secondEndpoint, firstAttachment, localOld, localFirst,
      localSecond, localThird, contactGadgetRightNode, contactGadgetSide]⟩
  · change i = 9 at h
    subst i
    refine ⟨Sum.inl (), ?_⟩
    cases negative <;> norm_num [contactPair, samePair, localToContact, localLeft, localRight,
      leftEdge, rightEdge, secondEndpoint, firstAttachment, localOld, localFirst,
      localSecond, localThird, contactGadgetRightNode, contactGadgetSide]
  · rcases h with ⟨rfl, rfl, rfl⟩
    exact ⟨rightEdge 0, by norm_num [contactPair, samePair, localToContact, localLeft, localRight,
      leftEdge, rightEdge, secondEndpoint, firstAttachment, localOld, localFirst,
      localSecond, localThird, contactGadgetRightNode, contactGadgetSide]⟩
  · exact right_adjacent_exists negative i j h
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨rightEdge 0, by norm_num [contactPair, samePair, localToContact, localLeft, localRight,
      leftEdge, rightEdge, secondEndpoint, firstAttachment, localOld, localFirst,
      localSecond, localThird, contactGadgetRightNode, contactGadgetSide]⟩
  · change j = 9 at h
    subst j
    refine ⟨Sum.inl (), ?_⟩
    cases negative <;> norm_num [contactPair, samePair, localToContact, localLeft, localRight,
      leftEdge, rightEdge, secondEndpoint, firstAttachment, localOld, localFirst,
      localSecond, localThird, contactGadgetRightNode, contactGadgetSide]
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨rightEdge 0, by norm_num [contactPair, samePair, localToContact, localLeft, localRight,
      leftEdge, rightEdge, secondEndpoint, firstAttachment, localOld, localFirst,
      localSecond, localThird, contactGadgetRightNode, contactGadgetSide]⟩
  · exact False.elim h

theorem contactLinked_symm (negative : Bool) {x y : ContactGadgetSite}
    (h : contactGadgetLinked negative x y) : contactGadgetLinked negative y x := by
  rcases x with i | (i | ⟨⟩) <;> rcases y with j | (j | ⟨⟩) <;>
    first | exact h | simpa only [contactGadgetLinked, Nat.dist_comm] using h

theorem contactLinked_iff (negative : Bool) (x y : LocalSite) :
    contactGadgetLinked negative (localToContact x) (localToContact y) ↔
      ∃ a, samePair (localLeft (if negative then 0 else 1) a) (localRight a) x y := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := contactLinked_exists negative (localToContact x) (localToContact y) h
    refine ⟨a, ?_⟩
    rcases ha with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact Or.inl ⟨localContactEquiv.injective hx, localContactEquiv.injective hy⟩
    · exact Or.inr ⟨localContactEquiv.injective hx, localContactEquiv.injective hy⟩
  · rintro ⟨a, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact localEdge_contactLinked negative a
    · exact contactLinked_symm negative (localEdge_contactLinked negative a)

/-- A contact link is an edge of the actual full graph. Consequently a
nonedge of that graph cannot be an unaccounted local contact. -/
theorem finalGraph_nonedge_contactNonlink {n r : ℕ} (F : Bonds n r) (W G : ℕ)
    (e : Fin r) (x y : LocalSite)
    (h : ¬∃ a, samePair ((finalGraph F W G).left a) ((finalGraph F W G).right a)
      (localVertex (F.left e) (F.right e) e x) (localVertex (F.left e) (F.right e) e y)) :
    ¬contactGadgetLinked (edgeNegative F e) (localToContact x) (localToContact y) := by
  intro hc
  obtain ⟨a, ha⟩ := (contactLinked_iff (edgeNegative F e) x y).mp hc
  rw [← member_edgeNegative F e] at ha
  apply h
  refine ⟨encodeEdge r e a, ?_⟩
  rw [finalGraph_left, finalGraph_right]
  exact samePair_map (localVertex (F.left e) (F.right e) e) ha

theorem exists_finalGraph_gadget_geometry {n r : ℕ} (F : Bonds n r) (W G : ℕ)
    (e : Fin r)
    (ℓ : Fin (r + ((r * 2 + r * 2 * 2) + (r * 2 + r * 2 * 2) * 2)) → ℝ)
    (hℓ : ∀ a, ℓ a ∈ Set.Icc (1 - contactLengthTolerance) (1 + contactLengthTolerance)) :
    ∃ P : LocalSite → ContactPoint,
      P (localOld 0) = contactPoint 0 0 ∧
      P (localOld 1) = contactPoint 17 0 ∧
      (∀ a, dist (P (localLeft (member (F.weight e)) a)) (P (localRight a)) = ℓ (encodeEdge r e a)) ∧
      (∀ x y, x ≠ y →
        (¬∃ a, samePair ((finalGraph F W G).left a) ((finalGraph F W G).right a)
          (localVertex (F.left e) (F.right e) e x) (localVertex (F.left e) (F.right e) e y)) →
        6 / 5 < dist (P x) (P y)) ∧
      (∀ x, dist (P x) (contactBaseGadgetPosition (edgeNegative F e) (localToContact x)) < 1 / 20) := by
  obtain ⟨P, h0, h1, hlinks, hnonlinks, hnear⟩ :=
    exists_local_geometry (edgeNegative F e) (fun a => ℓ (encodeEdge r e a))
      (fun a => hℓ (encodeEdge r e a))
  refine ⟨P, h0, h1, ?_, ?_, hnear⟩
  · intro a
    rw [member_edgeNegative]
    exact hlinks a
  · intro x y hxy h
    exact hnonlinks x y hxy (finalGraph_nonedge_contactNonlink F W G e x y h)

end ContinuumCoulomb.ContactMediator

end OAI
