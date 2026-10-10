import Mathlib

namespace OAI

/-!
Proper clauses choose distinct variables with independent fair signs. Formulas are
independent clause draws with replacement, and their satisfiability probability is
the literal finite cardinality ratio. The empty formula is satisfiable. When
there are fewer variables than literals, nonempty formula lengths have probability
zero by the convention that division by zero is zero.
The threshold assertion concerns fixed clause size and fixed density only, with
no assertion at the critical density.
-/

namespace FixedClauseThreshold

abbrev Assignment (n : ℕ) := Fin n → Bool

abbrev ProperClause (n k : ℕ) :=
  { C : Fin n → Option Bool // (Finset.univ.filter fun i => (C i).isSome).card = k }

abbrev Formula (n k m : ℕ) := Fin m → ProperClause n k

def SatisfiesClause {n k : ℕ} (σ : Assignment n) (C : ProperClause n k) : Prop :=
  ∃ i : Fin n, C.val i = some (σ i)

def Satisfies {n k m : ℕ} (σ : Assignment n) (F : Formula n k m) : Prop :=
  ∀ j, SatisfiesClause σ (F j)

def Satisfiable {n k m : ℕ} (F : Formula n k m) : Prop :=
  ∃ σ : Assignment n, Satisfies σ F

noncomputable def properSATProbability (n k m : ℕ) : ℝ := by
  classical
  exact (Fintype.card { F : Formula n k m // Satisfiable F } : ℝ) /
    (Fintype.card (Formula n k m) : ℝ)

def HasLimitingThreshold (k : ℕ) : Prop :=
  ∃ α : ℝ, 0 < α ∧
    (∀ c : ℝ, 0 ≤ c → c < α →
      Filter.Tendsto (fun n : ℕ => properSATProbability n k ⌊c * (n : ℝ)⌋₊)
        Filter.atTop (nhds 1)) ∧
    (∀ c : ℝ, α < c →
      Filter.Tendsto (fun n : ℕ => properSATProbability n k ⌊c * (n : ℝ)⌋₊)
        Filter.atTop (nhds 0))

end FixedClauseThreshold

end OAI
