import OAI.Probability.DilutedSpin.HistorySelector
import OAI.Probability.DilutedSpin.ShapeEmbedding

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators Classical
variable {Ω C ι : Type} [Fintype C] [DecidableEq C] [DecidableEq ι] {L : ℕ}

omit [Fintype C] [DecidableEq C] in
/-- A shape specified by a complete labeled splitting matrix contains each
of the target's branching vertices, with its vertex multiplicity intact. -/
lemma branchingCount_of_matrix (T S : PrescribedTree L) (q : C → T.Leaf)
    (hq : Function.Surjective q) (pos : C → S.Leaf)
    (h : ∀ a b, splitDepth S (pos a) (pos b) = splitDepth T (q a) (q b))
    (P : ℕ → Prop) : branchingCount T P ≤ branchingCount S P := by
  classical
  let e : SplitMap T S := {
    leaf := fun a => pos (Function.surjInv hq a)
    split := fun a b => (h _ _).trans
      (congrArg₂ (splitDepth T) (Function.surjInv_eq hq a) (Function.surjInv_eq hq b)) }
  exact e.branchingCount_le P

/-- Absolute projection-error cost for the ACTUAL exact-matrix history. This
is the charging step in the shifted-two-copy argument: take Q to be shifted
depths, so the old tree has no branching in Q. The exponent counts vertices,
not distinct depths, hence aligned copies are charged separately. -/
theorem prescribed_history_charging_bound (hL : 0 < L) (Q : Finset ℕ)
    (T S : PrescribedTree L) (q : C → T.Leaf) (hq : Function.Surjective q)
    (hS : branchingCount S (· ∈ Q) = 0)
    (W : (R : PrescribedTree L) → (C → R.Leaf) → (Sample Ω R → ℝ) → ℝ)
    (E : ℝ) (hE : 0 ≤ E)
    (hW : ∀ R pos g, (∀ x, |g x| ≤ 1) →
      (∀ a b, splitDepth R (pos a) (pos b) = splitDepth T (q a) (q b)) → |W R pos g| ≤ E)
    (cs : List C) (U : Finset ι) (loc : ι → S.Leaf) (pos : C → S.Leaf)
    (f : Sample Ω S → ℝ) (hf : ∀ x, |f x| ≤ 1) (hU : U.card ≤ leaves S) :
    |labeledHistory (grid L 0 L)
      (fun R pos g => if ∀ a b, splitDepth R (pos a) (pos b) = splitDepth T (q a) (q b)
        then W R pos g else 0) cs S U loc pos f| ≤
      E * (chargeBound (2*(leaves S+cs.length:ℕ)) ((Q.card:ℝ)*(leaves S+cs.length:ℕ))
        cs.length (branchingCount T (· ∈ Q)) * (L:ℝ)⁻¹^(branchingCount T (· ∈ Q))) := by
  classical
  apply labeledHistory_charging_bound hL Q (branchingCount T (· ∈ Q)) _ E hE cs S
    U loc pos f hf hU
  intro R loc g hg
  by_cases h : ∀ a b, splitDepth R (loc a) (loc b) = splitDepth T (q a) (q b)
  · rw [ite_eq_left h]
    have hc := branchingCount_of_matrix T R q hq loc h (· ∈ Q)
    rw [hS,zero_add,ite_eq_left hc,mul_one]
    exact hW R loc g hg h
  · rw [ite_eq_right h,abs_zero]
    exact mul_nonneg hE (by split_ifs <;> norm_num)

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
