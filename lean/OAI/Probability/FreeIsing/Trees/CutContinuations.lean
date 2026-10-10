import OAI.Probability.FreeIsing.Trees.RestrictedCutCardinality

namespace OAI

noncomputable section

namespace Problem367

private theorem isChain_append_iff_last {α : Type*} {R : α → α → Prop}
    (p q : List α) (hp : p ≠ []) :
    List.IsChain R (p ++ q) ↔
      List.IsChain R p ∧ List.IsChain R (p.getLast hp :: q) := by
  induction p with
  | nil => exact False.elim (hp rfl)
  | cons a p ih =>
    cases p with
    | nil => simp
    | cons b p =>
      simpa only [List.cons_append, List.isChain_cons_cons, List.getLast_cons_cons,
        and_assoc] using and_congr_right (fun _ : R a b => ih (by simp))

def cutLastColor {d k : ℕ} (v : TreeShell d (k + 1)) : Fin d :=
  v.1.1.getLast (by intro h; have hv := v.2; simp [h] at hv)

def appendCutContinuation {d k L : ℕ} (v : TreeShell d (k + 1))
    (w : ReducedTail (cutLastColor v) L) : TreeShell d (k + 1 + L) :=
  ⟨⟨v.1.1 ++ w.1,
    (isChain_append_iff_last v.1.1 w.1 (by intro h; have hv := v.2; simp [h] at hv)).mpr
      ⟨v.1.2, w.2.2⟩⟩, by simp [v.2, w.2.1]⟩

def cutPrefix {d k L : ℕ} (v : TreeShell d (k + 1 + L)) : TreeShell d (k + 1) :=
  ⟨⟨v.1.1.take (k + 1), v.1.2.take _⟩, by simp [List.length_take, v.2]⟩

@[simp] theorem cutPrefix_appendCutContinuation {d k L : ℕ}
    (v : TreeShell d (k + 1)) (w : ReducedTail (cutLastColor v) L) :
    cutPrefix (appendCutContinuation v w) = v := by
  apply Subtype.ext
  apply Subtype.ext
  simp [cutPrefix, appendCutContinuation, v.2]

def cutSuffix {d k L : ℕ} (v : TreeShell d (k + 1 + L)) :
    ReducedTail (cutLastColor (cutPrefix v)) L := by
  refine ⟨v.1.1.drop (k + 1), ?_, ?_⟩
  · simp [List.length_drop, v.2]
  · have h : List.IsChain (fun a b : Fin d => a ≠ b)
        (v.1.1.take (k + 1) ++ v.1.1.drop (k + 1)) := by
      rw [List.take_append_drop]
      exact v.1.2
    exact ((isChain_append_iff_last _ _
      (by intro heq; have := (cutPrefix v).2; simp [cutPrefix, heq] at this)).mp h).2

@[simp] theorem appendCutContinuation_prefix_suffix {d k L : ℕ}
    (v : TreeShell d (k + 1 + L)) :
    appendCutContinuation (cutPrefix v) (cutSuffix v) = v := by
  apply Subtype.ext
  apply Subtype.ext
  exact List.take_append_drop _ _

def cutContinuationEquiv (d k L : ℕ) :
    (Σ v : TreeShell d (k + 1), ReducedTail (cutLastColor v) L) ≃
      TreeShell d (k + 1 + L) :=
  Equiv.ofBijective (fun p => appendCutContinuation p.1 p.2) (by
    constructor
    · rintro ⟨v, w⟩ ⟨v', w'⟩ heq
      have hv : v = v' := by
        have := congrArg (@cutPrefix d k L) heq
        simpa only [cutPrefix_appendCutContinuation] using this
      subst v'
      have hw : w = w' := by
        apply Subtype.ext
        have hlist := congrArg (fun x : TreeShell d (k + 1 + L) => x.1.1) heq
        exact List.append_cancel_left hlist
      subst w'
      rfl
    · intro v
      exact ⟨⟨cutPrefix v, cutSuffix v⟩, appendCutContinuation_prefix_suffix v⟩)

theorem card_cutContinuations {d k : ℕ} (v : TreeShell d (k + 1)) (L : ℕ) :
    Fintype.card (ReducedTail (cutLastColor v) L) = (d - 1) ^ L :=
  card_reducedTail _ _

theorem sum_cutContinuations {M : Type*} [AddCommMonoid M]
    (d k L : ℕ) (f : TreeShell d (k + 1 + L) → M) :
    (∑ v : TreeShell d (k + 1 + L), f v) =
      ∑ p : TreeShell d (k + 1), ∑ w : ReducedTail (cutLastColor p) L,
        f (appendCutContinuation p w) := by
  rw [← (cutContinuationEquiv d k L).sum_comp f, Fintype.sum_sigma]
  rfl

def cutDescendants {d k : ℕ} (I : Finset (TreeShell d (k + 1))) (L : ℕ) :
    Finset (TreeShell d (k + 1 + L)) := by
  classical
  exact Finset.univ.filter (fun v => cutPrefix v ∈ I)

@[simp] theorem mem_cutDescendants {d k L : ℕ}
    (I : Finset (TreeShell d (k + 1))) (v : TreeShell d (k + 1 + L)) :
    v ∈ cutDescendants I L ↔ cutPrefix v ∈ I := by
  classical
  simp [cutDescendants]

theorem appendCutContinuation_descendant {d k L : ℕ}
    (v : TreeShell d (k + 1)) (w : ReducedTail (cutLastColor v) L) :
    v.1.1 <+: (appendCutContinuation v w).1.1 :=
  List.prefix_append _ _

theorem sum_cutDescendants {M : Type*} [AddCommMonoid M] {d k : ℕ}
    (I : Finset (TreeShell d (k + 1))) (L : ℕ)
    (f : TreeShell d (k + 1 + L) → M) :
    (∑ v ∈ cutDescendants I L, f v) =
      ∑ p ∈ I, ∑ w : ReducedTail (cutLastColor p) L, f (appendCutContinuation p w) := by
  classical
  have h := sum_cutContinuations d k L (fun v => if cutPrefix v ∈ I then f v else 0)
  simpa [cutDescendants, Finset.sum_filter] using h

@[simp] theorem card_cutDescendants {d k : ℕ}
    (I : Finset (TreeShell d (k + 1))) (L : ℕ) :
    (cutDescendants I L).card = I.card * (d - 1) ^ L := by
  classical
  have h := sum_cutDescendants I L (fun _ => (1 : ℕ))
  simpa using h

theorem average_cutDescendants {d k : ℕ}
    (I : Finset (TreeShell d (k + 1))) (L : ℕ)
    (f : TreeShell d (k + 1 + L) → ℝ) :
    (∑ v ∈ cutDescendants I L, f v) / ((cutDescendants I L).card : ℝ) =
      (∑ p ∈ I, (∑ w : ReducedTail (cutLastColor p) L, f (appendCutContinuation p w)) /
        (((d - 1) ^ L : ℕ) : ℝ)) / (I.card : ℝ) := by
  rw [sum_cutDescendants, card_cutDescendants, Nat.cast_mul,
    ← Finset.sum_div, div_div, mul_comm]

def rootPathVertex {d : ℕ} (v : TreeVertex d) (i : ℕ) : TreeVertex d :=
  ⟨v.1.take i, v.2.take i⟩

def rootPathProduct {d : ℕ} (a : TreeVertex d → ℝ) (v : TreeVertex d) : ℝ :=
  ∏ i ∈ Finset.range v.1.length, a (rootPathVertex v (i + 1))

def cutContinuationProduct {d k L : ℕ} (a : TreeVertex d → ℝ)
    (p : TreeShell d (k + 1)) (w : ReducedTail (cutLastColor p) L) : ℝ :=
  ∏ j ∈ Finset.range L,
    a (rootPathVertex (appendCutContinuation p w).1 (k + 1 + (j + 1)))

theorem rootPathProduct_le_cutContinuationProduct {d k L : ℕ}
    (a : TreeVertex d → ℝ) (ha : ∀ v, 0 ≤ a v ∧ a v ≤ 1)
    (p : TreeShell d (k + 1)) (w : ReducedTail (cutLastColor p) L) :
    rootPathProduct a (appendCutContinuation p w).1 ≤ cutContinuationProduct a p w := by
  unfold rootPathProduct
  rw [(appendCutContinuation p w).2, Finset.prod_range_add]
  have hpre : (∏ i ∈ Finset.range (k + 1),
      a (rootPathVertex (appendCutContinuation p w).1 (i + 1))) ≤ 1 :=
    Finset.prod_le_one₀ (fun i _ => (ha _).1) (fun i _ => (ha _).2)
  have htail : 0 ≤ (∏ j ∈ Finset.range L,
      a (rootPathVertex (appendCutContinuation p w).1 (k + 1 + j + 1))) :=
    Finset.prod_nonneg (fun j _ => (ha _).1)
  have h := mul_le_mul_of_nonneg_right hpre htail
  simpa only [one_mul, cutContinuationProduct, Nat.add_assoc] using h

theorem average_rootPathProduct_le_continuation_average {d k : ℕ}
    (a : TreeVertex d → ℝ) (ha : ∀ v, 0 ≤ a v ∧ a v ≤ 1)
    (I : Finset (TreeShell d (k + 1))) (L : ℕ) :
    (∑ v ∈ cutDescendants I L, rootPathProduct a v.1) /
        ((cutDescendants I L).card : ℝ) ≤
      (∑ p ∈ I, (∑ w : ReducedTail (cutLastColor p) L,
        cutContinuationProduct a p w) / (((d - 1) ^ L : ℕ) : ℝ)) / (I.card : ℝ) := by
  rw [average_cutDescendants]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro p hp
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum (fun w _ => rootPathProduct_le_cutContinuationProduct a ha p w)

theorem cutContinuation_vertex_descendant {d k L : ℕ}
    (p : TreeShell d (k + 1)) (w : ReducedTail (cutLastColor p) L) (j : ℕ) :
    p.1.1 <+:
      (rootPathVertex (appendCutContinuation p w).1 (k + 1 + (j + 1))).1 := by
  change p.1.1 <+: (p.1.1 ++ w.1).take (k + 1 + (j + 1))
  have htake : p.1.1.take (k + 1 + (j + 1)) = p.1.1 :=
    List.take_of_length_le (by rw [p.2]; omega)
  rw [List.take_append, htake]
  exact List.prefix_append _ _

theorem cutContinuationProduct_congr_on_descendants {d k L : ℕ}
    {a b : TreeVertex d → ℝ} (p : TreeShell d (k + 1))
    (w : ReducedTail (cutLastColor p) L)
    (hab : ∀ v : TreeVertex d, p.1.1 <+: v.1 → a v = b v) :
    cutContinuationProduct a p w = cutContinuationProduct b p w := by
  apply Finset.prod_congr rfl
  intro j hj
  exact hab _ (cutContinuation_vertex_descendant p w j)

private theorem shell_head_eq_first {d k : ℕ} (p : TreeShell d (k + 1)) :
    p.1.1.head? = some (treeShellSuccEquiv d k p).1 := by
  rcases p with ⟨⟨p, hp⟩, hlen⟩
  cases p with
  | nil => simp at hlen
  | cons a p => rfl

theorem mem_descendants_avoidingTreeCut {d k L : ℕ}
    (forbidden : Finset (Fin d)) (v : TreeShell d (k + 1 + L)) :
    v ∈ cutDescendants (avoidingTreeCut forbidden k) L ↔
      ∀ c ∈ v.1.1.head?, c ∉ forbidden := by
  classical
  rw [mem_cutDescendants, mem_avoidingTreeCut]
  have hhead : v.1.1.head? = (cutPrefix v).1.1.head? := by
    change v.1.1.head? = (v.1.1.take (k + 1)).head?
    cases v.1.1 <;> rfl
  rw [hhead, shell_head_eq_first]
  simp

end Problem367

end

end OAI
