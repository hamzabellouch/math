import OAI.Analysis.Nonexpansive.OrderedTree
import Mathlib.Order.KonigLemma
import Mathlib.Basic.Real.Basic

namespace OAI

/-!
# A feasible branch with finite prefix witnesses

Feasibility is an existential proposition on a finite node, so the feasible
nodes at each level still form a finite type. Restriction to an ancestor
preserves the same witness. The elementary graded form of König's lemma
then yields one coherent branch, with a witness for every finite prefix.

The witness set is arbitrary. In the fixed-point argument it is instantiated
with the whole unit ball of the closed difference span. No compactness or
surjectivity of projections between feasible levels is used here.
-/

namespace ReflexiveFixedPoints
namespace OrderedTree

variable (T : OrderedTree) {D : Type*}

/-- One witness satisfies every nonroot detector on the path to a node. -/
def DetectsPrefix (f : (k : ℕ) → T.Node k → D → ℝ)
    {n : ℕ} (v : T.Node n) (d : D) : Prop :=
  ∀ (i : ℕ) (hi : i ≤ n), 0 < i →
    (1 / 2 : ℝ) ≤ f i (T.ancestorLE hi v) d

/-- Feasibility retains membership in the given witness set. -/
def Feasible (B : Set D) (f : (k : ℕ) → T.Node k → D → ℝ)
    {n : ℕ} (v : T.Node n) : Prop :=
  ∃ d ∈ B, T.DetectsPrefix f v d

/-- A feasible node contains only a node and a proposition, not extra witness data. -/
abbrev FeasibleNode (B : Set D) (f : (k : ℕ) → T.Node k → D → ℝ)
    (n : ℕ) :=
  {v : T.Node n // T.Feasible B f v}

/-- All earlier coordinates of a branch are the actual ancestors. -/
def IsBranch (b : (n : ℕ) → T.Node n) : Prop :=
  ∀ ⦃i j : ℕ⦄ (hij : i ≤ j), T.ancestorLE hij (b j) = b i

variable (B : Set D) (f : (k : ℕ) → T.Node k → D → ℝ)

theorem detectsPrefix_zero (v : T.Node 0) (d : D) :
    T.DetectsPrefix f v d := by
  intro i hi hpos
  exact False.elim ((Nat.not_lt_of_ge hi) hpos)

theorem feasible_zero (hB : B.Nonempty) (v : T.Node 0) :
    T.Feasible B f v := by
  obtain ⟨d, hd⟩ := hB
  exact ⟨d, hd, T.detectsPrefix_zero f v d⟩

/-- Ancestor restriction keeps the original witness and every earlier constraint. -/
theorem detectsPrefix_ancestorLE {i j : ℕ} (hij : i ≤ j)
    {v : T.Node j} {d : D} (hd : T.DetectsPrefix f v d) :
    T.DetectsPrefix f (T.ancestorLE hij v) d := by
  intro k hk hpos
  rw [← T.ancestorLE_trans_apply hk hij]
  exact hd k (hk.trans hij) hpos

theorem feasible_ancestorLE {i j : ℕ} (hij : i ≤ j)
    {v : T.Node j} (hv : T.Feasible B f v) :
    T.Feasible B f (T.ancestorLE hij v) := by
  obtain ⟨d, hdB, hd⟩ := hv
  exact ⟨d, hdB, T.detectsPrefix_ancestorLE f hij hd⟩

/-- A feasible node at every depth yields a coherent feasible branch. -/
theorem exists_feasible_branch
    (hne : ∀ n, ∃ v : T.Node n, T.Feasible B f v) :
    ∃ b : (n : ℕ) → T.Node n,
      T.IsBranch b ∧ ∀ n, T.Feasible B f (b n) := by
  classical
  let : ∀ n, Nonempty (T.FeasibleNode B f n) := fun n => by
    obtain ⟨v, hv⟩ := hne n
    exact ⟨⟨v, hv⟩⟩
  let π : {i j : ℕ} → i ≤ j → T.FeasibleNode B f j → T.FeasibleNode B f i :=
    fun {_ _} hij v => ⟨T.ancestorLE hij v.val,
      T.feasible_ancestorLE B f hij v.property⟩
  have hπrefl : ∀ ⦃i⦄ (v : T.FeasibleNode B f i), π (le_refl i) v = v := by
    intro i v
    apply Subtype.ext
    exact T.ancestorLE_refl_apply i v.val
  have hπtrans : ∀ ⦃i j k⦄ (hij : i ≤ j) (hjk : j ≤ k)
      (v : T.FeasibleNode B f k),
      π hij (π hjk v) = π (hij.trans hjk) v := by
    intro i j k hij hjk v
    apply Subtype.ext
    exact (T.ancestorLE_trans_apply hij hjk v.val).symm
  obtain ⟨b, hb⟩ := exists_seq_forall_proj_of_forall_finite
    (α := fun n => T.FeasibleNode B f n) π hπrefl hπtrans
    (fun _ _ => Set.toFinite _)
  refine ⟨fun n => (b n).val, ?_, fun n => (b n).property⟩
  intro i j hij
  exact congrArg (fun v : T.FeasibleNode B f i => v.val) (hb hij)

/-- Prefix feasibility written directly in the coherent branch coordinates. -/
theorem exists_feasible_branch_with_witnesses
    (hne : ∀ n, ∃ v : T.Node n, T.Feasible B f v) :
    ∃ b : (n : ℕ) → T.Node n,
      T.IsBranch b ∧
      ∀ n, ∃ d ∈ B, ∀ i, 0 < i → i ≤ n →
        (1 / 2 : ℝ) ≤ f i (b i) d := by
  obtain ⟨b, hb, hfeasible⟩ := T.exists_feasible_branch B f hne
  refine ⟨b, hb, ?_⟩
  intro n
  obtain ⟨d, hdB, hd⟩ := hfeasible n
  refine ⟨d, hdB, ?_⟩
  intro i hpos hin
  have hi := hd i hin hpos
  rw [hb hin] at hi
  exact hi

/-- The positive-depth finite witness theorem suffices; depth zero uses any element of B. -/
theorem exists_branch_of_finite_witnesses (hB : B.Nonempty)
    (hfinite : ∀ n, 0 < n → ∃ v : T.Node n,
      ∃ d ∈ B, T.DetectsPrefix f v d) :
    ∃ b : (n : ℕ) → T.Node n,
      T.IsBranch b ∧
      ∀ n, ∃ d ∈ B, ∀ i, 0 < i → i ≤ n →
        (1 / 2 : ℝ) ≤ f i (b i) d := by
  apply T.exists_feasible_branch_with_witnesses B f
  intro n
  cases n with
  | zero => exact ⟨T.root, T.feasible_zero B f hB T.root⟩
  | succ n => exact hfinite (n + 1) (Nat.succ_pos n)

theorem IsBranch.root_eq {b : (n : ℕ) → T.Node n} (_hb : T.IsBranch b) :
    b 0 = T.root :=
  T.eq_root (b 0)

theorem IsBranch.parent_eq {b : (n : ℕ) → T.Node n}
    (hb : T.IsBranch b) (n : ℕ) :
    T.parent n (b (n + 1)) = b n := by
  simpa only [T.ancestorLE_succ_apply] using hb (Nat.le_succ n)

end OrderedTree
end ReflexiveFixedPoints

end OAI
