import OAI.Probability.FreeIsing.Trees.ConnectedHull
import OAI.Probability.FreeIsing.Trees.WordAction

namespace OAI

noncomputable section

namespace Problem367.TreeKoopman

theorem wordAut_append_apply {d : ℕ} (u w : List (Fin d)) (v : TreeVertex d) :
    (wordAut (u ++ w)).toEquiv v =
      (wordAut u).toEquiv ((wordAut w).toEquiv v) := by
  induction u with
  | nil => rfl
  | cons c u ih =>
    change prefixFlip c ((wordAut (u ++ w)).toEquiv v) =
      prefixFlip c ((wordAut u).toEquiv ((wordAut w).toEquiv v))
    rw [ih]

theorem wordAut_reverse_left_apply {d : ℕ} (w : List (Fin d)) (v : TreeVertex d) :
    (wordAut w.reverse).toEquiv ((wordAut w).toEquiv v) = v := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    rw [List.reverse_cons, wordAut_append_apply]
    change (wordAut w.reverse).toEquiv
      (prefixFlip c (prefixFlip c ((wordAut w).toEquiv v))) = v
    rw [prefixFlip_twice, ih]

theorem wordAut_reverse_right_apply {d : ℕ} (w : List (Fin d)) (v : TreeVertex d) :
    (wordAut w).toEquiv ((wordAut w.reverse).toEquiv v) = v := by
  simpa only [List.reverse_reverse] using wordAut_reverse_left_apply w.reverse v

theorem wordAut_reverse_apply_eq_symm {d : ℕ} (w : List (Fin d)) (v : TreeVertex d) :
    (wordAut w.reverse).toEquiv v = (wordAut w).toEquiv.symm v := by
  apply (wordAut w).toEquiv.injective
  rw [wordAut_reverse_right_apply, Equiv.apply_symm_apply]

def reverseVertex {d : ℕ} (v : TreeVertex d) : TreeVertex d :=
  ⟨v.1.reverse, by
    change List.IsChain (fun a b => a ≠ b) v.1.reverse
    rw [List.isChain_reverse]
    exact v.2.imp (fun _ _ h => Ne.symm h)⟩

@[simp] theorem reverseVertex_twice {d : ℕ} (v : TreeVertex d) :
    reverseVertex (reverseVertex v) = v := by
  apply Subtype.ext
  exact List.reverse_reverse v.1

theorem wordAut_append_reverse_suffix {d : ℕ} (u w : TreeVertex d) :
    (wordAut (u.1 ++ w.1)).toEquiv (reverseVertex w) = u := by
  rw [wordAut_append_apply]
  have hw : reverseVertex w =
      (wordAut w.1.reverse).toEquiv ⟨[], List.IsChain.nil⟩ :=
    (wordAut_root w.1.reverse (reverseVertex w).2).symm
  rw [hw, wordAut_reverse_right_apply, wordAut_root u.1 u.2]

theorem wordAut_apply_reverse_prefix {d : ℕ} (v : TreeVertex d) (k : ℕ) :
    (wordAut v.1).toEquiv (ConnectedHull.takeVertex (reverseVertex v) k) =
      ConnectedHull.takeVertex v (v.1.length - k) := by
  let u : TreeVertex d := ConnectedHull.takeVertex v (v.1.length - k)
  let w : TreeVertex d := ⟨v.1.drop (v.1.length - k), v.2.drop _⟩
  have hsplit : u.1 ++ w.1 = v.1 := List.take_append_drop _ _
  have hrev : ConnectedHull.takeVertex (reverseVertex v) k = reverseVertex w := by
    apply Subtype.ext
    exact List.take_reverse
  calc
    (wordAut v.1).toEquiv (ConnectedHull.takeVertex (reverseVertex v) k) =
        (wordAut (u.1 ++ w.1)).toEquiv (reverseVertex w) := by rw [hsplit, hrev]
    _ = u := wordAut_append_reverse_suffix u w

theorem wordAut_reverseVertex {d : ℕ} (v : TreeVertex d) :
    (wordAut v.1).toEquiv (reverseVertex v) = ConnectedHull.root d := by
  have h := wordAut_apply_reverse_prefix v v.1.length
  have htake : ConnectedHull.takeVertex (reverseVertex v) v.1.length = reverseVertex v := by
    apply Subtype.ext
    change v.1.reverse.take v.1.length = v.1.reverse
    simpa only [List.length_reverse] using (List.take_length (l := v.1.reverse))
  rw [htake] at h
  simpa [ConnectedHull.takeVertex, ConnectedHull.root] using h

theorem wordAut_reverse_prefix_edge {d : ℕ} (v : TreeVertex d) (k : ℕ) :
    (wordAut v.1).toEquiv (ConnectedHull.takeVertex (reverseVertex v) k) =
        ConnectedHull.takeVertex v (v.1.length - k) ∧
    (wordAut v.1).toEquiv (ConnectedHull.takeVertex (reverseVertex v) (k + 1)) =
        ConnectedHull.takeVertex v (v.1.length - (k + 1)) :=
  ⟨wordAut_apply_reverse_prefix v k, wordAut_apply_reverse_prefix v (k + 1)⟩

end Problem367.TreeKoopman

end

end OAI
