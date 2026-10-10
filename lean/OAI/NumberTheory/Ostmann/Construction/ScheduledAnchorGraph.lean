import OAI.NumberTheory.Ostmann.Construction.GraphCopySchedule
import OAI.NumberTheory.Ostmann.Construction.FinalGraphIdentification

namespace OAI

/-! # Anchor codes derived from the full copied-slot schedule -/

namespace Ostmann

open scoped Classical

/-- Every outgoing word-to-anchor edge is its final copy parity. -/
theorem copyScheduleGraph_path_to_anchor {I : Type*}
    (g : I → I → ℤ) (pivot : ℕ → I) (n : ℕ) (i a : I)
    (hp : ∀ k < n, g i (pivot k) = 1) (ha : g i a = 1)
    (t : Fin n → Bool) (j : ℕ) (hj : j < n) (b : Bool) :
    copyScheduleGraph g pivot n (copySchedulePath n t i) (copyScheduleAnchor n j b a) =
      finalCopyParity t := by
  induction n with
  | zero => omega
  | succ n ih =>
    have hprev : ∀ k < n, g i (pivot k) = 1 := fun k hk => hp k (by omega)
    have ht : Fin.snoc (fun k => t k.castSucc) (t (Fin.last n)) = t :=
      Fin.snoc_init_self t
    by_cases hjn : j = n
    · subst j
      have hanc : copyScheduleAnchor (n + 1) n b a =
          Sum.inl (b, copyScheduleOutside n a) := copyScheduleAnchor_new n b a
      rw [hanc]
      change (if t (Fin.last n) = b then
        transferCopySign (t (Fin.last n)) * copyScheduleGraph g pivot n
          (copySchedulePath n (fun k => t k.castSucc) i) (copyScheduleOutside n a)
        else transferCopySign (t (Fin.last n)) * copyScheduleGraph g pivot n
          (copySchedulePath n (fun k => t k.castSucc) i) (copySchedulePositive n (pivot n))) = _
      rw [copyScheduleGraph_path_to_fresh g pivot n i a ha,
        copyScheduleGraph_path_to_positive g pivot n i (pivot n) hprev (hp n (by omega))]
      rw [← ht, finalCopyParity_snoc]
      simp
    · have hj' : j < n := by omega
      have hanc : copyScheduleAnchor (n + 1) j b a =
          Sum.inr (copyScheduleAnchor n j b a) := copyScheduleAnchor_old n _ b a hjn
      rw [hanc]
      change transferCopySign (t (Fin.last n)) * copyScheduleGraph g pivot n
        (copySchedulePath n (fun k => t k.castSucc) i) (copyScheduleAnchor n j b a) = _
      rw [ih hprev (fun k => t k.castSucc) hj']
      rw [← ht, finalCopyParity_snoc]
      simp

/-- The incoming anchor edge has exactly the previously constructed code.
The initial graph is the only source of the two hypotheses. -/
theorem copyScheduleGraph_anchor_to_path {I : Type*}
    (g : I → I → ℤ) (pivot : ℕ → I) (n : ℕ) (i a : I)
    (hp : ∀ k < n, g a (pivot k) = 1) (ha : g a i = 1)
    (t : Fin n → Bool) (j : Fin n) (b : Bool) :
    copyScheduleGraph g pivot n (copyScheduleAnchor n j b a) (copySchedulePath n t i) =
      anchorIncoming (fun _ => 1) t j b := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    have ht : Fin.snoc (fun k => t k.castSucc) (t (Fin.last n)) = t :=
      Fin.snoc_init_self t
    have hprev : ∀ k < n, g a (pivot k) = 1 := fun k hk => hp k (by omega)
    by_cases hjn : j.val = n
    · have hjlast : j = Fin.last n := Fin.ext hjn
      subst j
      let G := fun x y => copyScheduleGraph g pivot n
        (copySchedulePredecessor (copySchedulePositive n (pivot n)) x)
        (copySchedulePredecessor (copySchedulePositive n (pivot n)) y)
      have hinc : G (some (.inl (copyScheduleOutside n a)))
          (some (.inl (copySchedulePath n (fun k => t k.castSucc) i))) =
            finalCopyParity (fun k => t k.castSucc) := by
        change copyScheduleGraph g pivot n (copyScheduleOutside n a)
          (copySchedulePath n (fun k => t k.castSucc) i) = _
        rw [copyScheduleGraph_fresh_to_path, ha, mul_one]
      have hpiv : G (some (.inl (copyScheduleOutside n a))) none = 1 := by
        change copyScheduleGraph g pivot n (copyScheduleOutside n a)
          (copySchedulePositive n (pivot n)) = _
        rw [copyScheduleGraph_fresh_to_positive, hp n (by omega)]
      have hc := anchorIncoming_created_by_transfer G (copyScheduleOutside n a)
        (copySchedulePath n (fun k => t k.castSucc) i)
        (α := fun _ => 1) (fun k => t k.castSucc) (t (Fin.last n)) b hinc hpiv
      have he : copyScheduleGraph g pivot (n + 1)
          (Sum.inl (b, copyScheduleOutside n a))
          (Sum.inl (t (Fin.last n), copySchedulePath n (fun k => t k.castSucc) i)) =
            anchorIncoming (fun _ => 1) (Fin.snoc (fun k => t k.castSucc) (t (Fin.last n)))
              (Fin.last n) b := hc.symm
      rw [ht] at he
      have hanc : copyScheduleAnchor (n + 1) n b a =
          Sum.inl (b, copyScheduleOutside n a) := copyScheduleAnchor_new n b a
      rw [show (Fin.last n).val = n from rfl, hanc]
      exact he
    · let j' : Fin n := ⟨j.val, by omega⟩
      have hjcast : j'.castSucc = j := Fin.ext rfl
      have hanc : copyScheduleAnchor (n + 1) j b a =
          Sum.inr (copyScheduleAnchor n j b a) := copyScheduleAnchor_old n _ b a hjn
      rw [hanc]
      change transferCopySign (t (Fin.last n)) * copyScheduleGraph g pivot n
        (copyScheduleAnchor n j b a) (copySchedulePath n (fun k => t k.castSucc) i) = _
      rw [ih hprev (fun k => t k.castSucc) j']
      rw [← ht, ← hjcast, anchorIncoming_snoc_old]
      simp

/-- The level-zero graph has exponent one on every distinct ordered pair. -/
noncomputable def initialCompleteGraph {I : Type*} (i j : I) : ℤ :=
  if i = j then 0 else 1

@[simp] theorem initialCompleteGraph_self {I : Type*} (i : I) :
    initialCompleteGraph i i = 0 := by simp [initialCompleteGraph]

theorem initialCompleteGraph_of_ne {I : Type*} {i j : I} (h : i ≠ j) :
    initialCompleteGraph i j = 1 := by simp [initialCompleteGraph, h]

/-- The final graph is obtained by restricting the computed graph to the
surviving words, anchors, and remaining slots. -/
noncomputable def scheduledFinalGraph {I J : Type*} {n m : ℕ}
    (pivot : ℕ → I) (word : Fin m → I) (anchor : Fin (n + 1) → I)
    (other : J → CopyScheduleVertex I (n + 1)) :
    FinalGraphVertex n m J → FinalGraphVertex n m J → ℤ :=
  let vertex : FinalGraphVertex n m J → CopyScheduleVertex I (n + 1) := fun x =>
    match x with
    | .inl (t, i) => copySchedulePath (n + 1) (parityPathValue t) (word i)
    | .inr (.inl (j, b)) => copyScheduleAnchor (n + 1) j b (anchor j)
    | .inr (.inr j) => other j
  fun x y => copyScheduleGraph initialCompleteGraph pivot (n + 1) (vertex x) (vertex y)

theorem scheduledFinalGraph_diagonal {I J : Type*} {n m : ℕ}
    (pivot : ℕ → I) (word : Fin m → I) (anchor : Fin (n + 1) → I)
    (other : J → CopyScheduleVertex I (n + 1)) (x : FinalGraphVertex n m J) :
    scheduledFinalGraph pivot word anchor other x x = 0 :=
  copyScheduleGraph_diagonal initialCompleteGraph pivot initialCompleteGraph_self _ _

/-- Every distinct parity-preserving reassignment of the actual scheduled
 graph has the required signed-square edge and zero reverse edge. -/
theorem scheduledFinalGraph_reassignment {I J : Type*} {n m : ℕ}
    (pivot : ℕ → I) (word : Fin m → I) (anchor : Fin (n + 1) → I)
    (other : J → CopyScheduleVertex I (n + 1))
    (hwp : ∀ i k, k < n + 1 → word i ≠ pivot k)
    (hpa : ∀ j k, k < n + 1 → anchor j ≠ pivot k)
    (hwa : ∀ i j, word i ≠ anchor j)
    (e f : FinalParityReassignments n m) (hef : e ≠ f) :
    ∃ (x : ParityPathSum n × Fin m) (j : Fin (n + 1)) (b : Bool),
      let G := graphDifference
        (finalReassignedGraph (scheduledFinalGraph pivot word anchor other) e)
        (finalReassignedGraph (scheduledFinalGraph pivot word anchor other) f)
      (G (.inr (.inl (j, b))) (.inl x) = 2 ∨
        G (.inr (.inl (j, b))) (.inl x) = -2) ∧
      G (.inl x) (.inr (.inl (j, b))) = 0 := by
  apply final_reassignment_graph_interaction _ (fun _ => 1)
    (fun _ => Or.inl rfl) ?_ ?_ e f hef
  · intro x j b
    apply copyScheduleGraph_anchor_to_path
    · intro k hk
      exact initialCompleteGraph_of_ne (hpa j k hk)
    · exact initialCompleteGraph_of_ne (hwa x.2 j).symm
  · intro x j b
    apply copyScheduleGraph_path_to_anchor
    · intro k hk
      exact initialCompleteGraph_of_ne (hwp x.2 k hk)
    · exact initialCompleteGraph_of_ne (hwa x.2 j)
    · exact j.isLt

end Ostmann

end OAI
