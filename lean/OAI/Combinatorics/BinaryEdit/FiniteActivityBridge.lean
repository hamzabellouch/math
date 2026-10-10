import OAI.Combinatorics.BinaryEdit.Branching
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

namespace OAI

/-!
# Finite indices for the sparse-activity obstruction

Internal nodes are indexed by their depth and finite sequence of child
indices. Absence of a sparse active node bounds the cardinality of active
leaves, which controls the Fourier mass.
-/

noncomputable section

namespace TreeEdit.BinaryLower.FiniteActivity

open Classical

/-- All internal nodes of a complete tree of depth `h`. -/
abbrev InternalNode (α : Type*) (h : ℕ) := Σ j : Fin h, Fin (j : ℕ) → α

/-- A bad node is active but has fewer than `b` active children. -/
def sparseNode {α : Type*} [Fintype α] {h : ℕ}
    (active : List α → Prop) (b : ℕ) (v : InternalNode α h) : Prop :=
  active (List.ofFn v.2) ∧
    Branching.activeChildCount active (List.ofFn v.2) < b

/-- Absence of bad nodes in the finite node indexing gives the full active
leaf cardinality lower bound. -/
theorem dense_of_no_sparse {α : Type*} [Fintype α]
    (active : List α → Prop) (b h : ℕ)
    (hroot : active []) (hno : ¬ ∃ v : InternalNode α h, sparseNode active b v) :
    b ^ h ≤ (Finset.univ.filter fun f : Fin h → α => active (List.ofFn f)).card := by
  classical
  have hlocal : ∀ p : List α, p.length < h → active p →
      b ≤ Branching.activeChildCount active p := by
    intro p hp ha
    by_contra hb
    have hsmall : Branching.activeChildCount active p < b := Nat.lt_of_not_ge hb
    let v : InternalNode α h := ⟨⟨p.length, hp⟩, p.get⟩
    apply hno
    refine ⟨v, ?_⟩
    simpa [sparseNode, v] using And.intro ha hsmall
  have hbranch := Branching.branchesAtLeast_of_local active b h h hlocal [] (by simp)
  simpa only [List.nil_append] using
    Branching.pow_le_card_active_paths active b h [] hbranch hroot

/-- Character formulation of the sparse-node predicate. -/
def characterSparse {α G : Type*} [Fintype α] [AddCommGroup G] {h : ℕ}
    (w : List α → G) (b : ℕ) (v : InternalNode α h) (χ : AddChar G ℂ) : Prop :=
  sparseNode (fun p => χ (w p) ≠ 1) b v

/-- For a root-active character that escapes every sparse-node test, the
number of active terminal vectors is at least the branching factor to the
height. -/
theorem character_dense_of_no_sparse {α G : Type*}
    [Fintype α] [AddCommGroup G]
    (w : List α → G) (b h : ℕ) (χ : AddChar G ℂ)
    (hroot : χ (w []) ≠ 1)
    (hno : ¬ ∃ v : InternalNode α h, characterSparse w b v χ) :
    (b : ℝ) ^ h ≤
      ((Finset.univ.filter fun f : Fin h → α => χ (w (List.ofFn f)) ≠ 1).card : ℝ) := by
  classical
  have hd := dense_of_no_sparse (fun p => χ (w p) ≠ 1) b h hroot hno
  exact_mod_cast hd

/-- Adapter to the actual cyclic coordinate generators used by the spectral
leaf tests. The only structural identity needed here is `w_leaf = e_leaf`. -/
theorem character_dense_of_leaf_generators {α G : Type*}
    [Fintype α] [AddCommGroup G]
    (w : List α → G) (b h : ℕ) (e : (Fin h → α) → G) (χ : AddChar G ℂ)
    (hgen : ∀ f : Fin h → α, w (List.ofFn f) = e f)
    (hroot : χ (w []) ≠ 1)
    (hno : ¬ ∃ v : InternalNode α h, characterSparse w b v χ) :
    (b : ℝ) ^ h ≤
      ((Finset.univ.filter fun f : Fin h → α => χ (e f) ≠ 1).card : ℝ) := by
  classical
  simpa only [hgen] using character_dense_of_no_sparse w b h χ hroot hno


/-- Exact sum of the reciprocal-subtree budgets over the finite internal-node
index. The result is independent of the branching width. -/
theorem internal_node_budget (m h : ℕ) (hm : m ≠ 0) (C : ℝ) :
    (∑ v : InternalNode (Fin m) h, C / (m : ℝ) ^ (v.1 : ℕ)) = h * C := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  rw [Fintype.sum_sigma]
  have hlevel : ∀ j : Fin h,
      (∑ _f : Fin (j : ℕ) → Fin m, C / (m : ℝ) ^ (j : ℕ)) = C := by
    intro j
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
    rw [mul_comm, div_mul_cancel₀ _ (pow_ne_zero _ hm')]
  simp only [hlevel, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The leaf-coordinate edit budgets sum to exactly the word length. -/
theorem leaf_budget (m h : ℕ) (hm : m ≠ 0) (M : ℝ) :
    (∑ _f : Fin h → Fin m, M / (m : ℝ) ^ h) = M := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
  rw [mul_comm, div_mul_cancel₀ _ (pow_ne_zero _ hm')]

end TreeEdit.BinaryLower.FiniteActivity

end

end OAI
