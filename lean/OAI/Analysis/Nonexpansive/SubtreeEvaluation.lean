import OAI.Analysis.Nonexpansive.TreeEvaluation

namespace OAI

/-!
# Actual evaluation of a subtree

Evaluation between two arbitrary levels is an iteration of the same
`collapse` operation used by root evaluation. The cutoff's own maps are
not applied. Composition gives both the root factorization and the
recurrence at the top of a subtree.
-/

open scoped BigOperators

namespace ReflexiveFixedPoints

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

namespace TreeEvaluation

variable {T : OrderedTree} {W : WeightedTree T} {K : Set X}
variable (E : TreeEvaluation W K)

/-- The actual outputs between two levels, formed by iterating `collapse`. -/
noncomputable def subtreeOutput {i j : ℕ} (h : i ≤ j) :
    (T.Node j → K) → T.Node i → K :=
  Nat.leRec (motive := fun n _ => (T.Node n → K) → T.Node i → K)
    id (fun {n} _ f H => f (E.collapse n H)) h

@[simp] theorem subtreeOutput_refl_apply (i : ℕ) (H : T.Node i → K) :
    E.subtreeOutput (Nat.le_refl i) H = H := by
  simp only [subtreeOutput, Nat.leRec_self, id_eq]

/-- Peel off the collapse immediately above the cutoff level. -/
theorem subtreeOutput_step {i j : ℕ} (h : i ≤ j) {h' : i ≤ j + 1}
    (H : T.Node (j + 1) → K) :
    E.subtreeOutput h' H = E.subtreeOutput h (E.collapse j H) := by
  unfold subtreeOutput
  rw [Nat.leRec_succ _ _ h]

@[simp] theorem subtreeOutput_succ (i : ℕ) (H : T.Node (i + 1) → K) :
    E.subtreeOutput (Nat.le_succ i) H = E.collapse i H := by
  rw [E.subtreeOutput_step (Nat.le_refl i), E.subtreeOutput_refl_apply]

/-- Evaluating through two consecutive intervals equals their actual composite. -/
theorem subtreeOutput_comp {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (H : T.Node k → K) :
    E.subtreeOutput hij (E.subtreeOutput hjk H) =
      E.subtreeOutput (hij.trans hjk) H := by
  induction hjk using Nat.leRec with
  | refl => simp only [E.subtreeOutput_refl_apply]
  | @le_succ_of_le k hjk ih =>
      rw [E.subtreeOutput_step hjk, E.subtreeOutput_step (hij.trans hjk)]
      exact ih (E.collapse k H)

/-- The recursive rule at the top of a subtree uses its actual child outputs. -/
theorem subtreeOutput_top_step {i j : ℕ} (h : i ≤ j) (hnext : i + 1 ≤ j)
    (H : T.Node j → K) :
    E.subtreeOutput h H = E.collapse i (E.subtreeOutput hnext H) := by
  calc
    E.subtreeOutput h H =
        E.subtreeOutput (Nat.le_succ i) (E.subtreeOutput hnext H) :=
      (E.subtreeOutput_comp (Nat.le_succ i) hnext H).symm
    _ = _ := E.subtreeOutput_succ i _

theorem subtreeOutput_top_step_apply {i j : ℕ} (h : i ≤ j) (hnext : i + 1 ≤ j)
    (H : T.Node j → K) (v : T.Node i) :
    E.subtreeOutput h H v =
      E.map i v (E.childAverage i (E.subtreeOutput hnext H) v) := by
  rw [E.subtreeOutput_top_step h hnext H]
  rfl

/-- Root evaluation factorizes through the actual outputs at every intermediate level. -/
theorem evaluate_subtreeOutput {i j : ℕ} (h : i ≤ j) (H : T.Node j → K) :
    E.evaluate j H = E.evaluate i (E.subtreeOutput h H) := by
  induction h using Nat.leRec with
  | refl => simp only [E.subtreeOutput_refl_apply]
  | @le_succ_of_le j h ih =>
      rw [E.evaluate_succ, E.subtreeOutput_step h]
      exact ih (E.collapse j H)

@[simp] theorem subtreeOutput_zero_root (j : ℕ) (H : T.Node j → K) :
    E.subtreeOutput (Nat.zero_le j) H T.root = E.evaluate j H := by
  simpa only [E.evaluate_zero] using (E.evaluate_subtreeOutput (Nat.zero_le j) H).symm

/-- The inequality-indexed and distance-indexed implementations coincide. -/
theorem subtreeOutput_eq_evaluateFrom (i d : ℕ) (H : T.Node (i + d) → K) :
    E.subtreeOutput (Nat.le_add_right i d) H = E.evaluateFrom i d H := by
  induction d with
  | zero => simp only [Nat.add_zero, E.subtreeOutput_refl_apply, E.evaluateFrom_zero]
  | succ d ih =>
      rw [E.subtreeOutput_step (Nat.le_add_right i d), E.evaluateFrom_succ]
      exact ih (E.collapse (i + d) H)

/-- A child average depends only on the children belonging to that parent. -/
theorem childAverage_congr (k : ℕ) (H H' : T.Node (k + 1) → K)
    (p : T.Node k) (heq : ∀ c, T.parent k c = p → H c = H' c) :
    E.childAverage k H p = E.childAverage k H' p := by
  apply Subtype.ext
  simp only [E.childAverage_val]
  apply Finset.sum_congr rfl
  intro c hc
  rw [heq c (Finset.mem_filter.mp hc).2]

/-- The nonlinear parent map preserves equality of its actual child input. -/
theorem collapse_congr (k : ℕ) (H H' : T.Node (k + 1) → K)
    (p : T.Node k) (heq : ∀ c, T.parent k c = p → H c = H' c) :
    E.collapse k H p = E.collapse k H' p := by
  unfold collapse
  rw [E.childAverage_congr k H H' p heq]

/-- A subtree output depends only on the cutoff values below that node. -/
theorem subtreeOutput_congr {i j : ℕ} (h : i ≤ j) :
    ∀ (H H' : T.Node j → K) (v : T.Node i),
      (∀ s, T.ancestorLE h s = v → H s = H' s) →
      E.subtreeOutput h H v = E.subtreeOutput h H' v := by
  induction h using Nat.leRec with
  | refl =>
      intro H H' v heq
      simpa only [E.subtreeOutput_refl_apply] using heq v (by simp)
  | @le_succ_of_le j h ih =>
      intro H H' v heq
      rw [E.subtreeOutput_step h, E.subtreeOutput_step h]
      apply ih (E.collapse j H) (E.collapse j H') v
      intro p hp
      apply E.collapse_congr j H H' p
      intro c hc
      apply heq c
      rw [T.ancestorLE_step_apply h, hc]
      exact hp

theorem subtreeOutput_congr_of_descendants {i j : ℕ} (h : i ≤ j)
    (H H' : T.Node j → K) (v : T.Node i)
    (heq : ∀ s ∈ T.descendants h v, H s = H' s) :
    E.subtreeOutput h H v = E.subtreeOutput h H' v := by
  apply E.subtreeOutput_congr h H H' v
  intro s hs
  exact heq s ((T.mem_descendants h v s).2 hs)

end TreeEvaluation
end ReflexiveFixedPoints

end OAI
