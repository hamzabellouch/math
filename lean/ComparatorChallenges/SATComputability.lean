import Mathlib

namespace OAI

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
end FixedClauseThreshold

namespace FixedClauseThreshold.Computability

open Filter
open scoped Topology NNReal

def MainStatement : Prop :=
    ∃ (α : ℝ) (q : ℕ → ℚ) (c : Nat.Partrec.Code),
      0 < α ∧
      (∀ a : ℝ, 0 ≤ a → a < α →
        Tendsto (fun n : ℕ => properSATProbability n 3 ⌊a*(n : ℝ)⌋₊) atTop (nhds 1)) ∧
      (∀ a : ℝ, α < a →
        Tendsto (fun n : ℕ => properSATProbability n 3 ⌊a*(n : ℝ)⌋₊) atTop (nhds 0)) ∧
      Computable (fun r => Encodable.encode (q r)) ∧
      (∀ r, c.eval r = Part.some (Encodable.encode (q r))) ∧
      (∀ r, |(q r : ℝ)-α| ≤ (2^r : ℝ)⁻¹)

theorem main : MainStatement := by
  sorry

end FixedClauseThreshold.Computability

end OAI
