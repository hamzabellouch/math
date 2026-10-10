import OAI.NumberTheory.TwoPoint.Circuits.CircuitDecisionDNF

namespace OAI

/-! Decision-tree certificates are preserved by fixing additional coordinates.
We also package the two Boolean polarities of a certificate. -/

namespace TwoPointCorrelations

open scoped Classical

namespace BooleanDecisionTree

def restrict {n : ℕ} (ρ : PartialAssignment n) :
    BooleanDecisionTree n → BooleanDecisionTree n
  | .leaf b => .leaf b
  | .query i low high =>
    match ρ i with
    | none => .query i (low.restrict ρ) (high.restrict ρ)
    | some false => low.restrict ρ
    | some true => high.restrict ρ

@[simp] theorem restrict_eval {n : ℕ} (T : BooleanDecisionTree n)
    (ρ : PartialAssignment n) (x : BooleanCube n) :
    (T.restrict ρ).eval x = T.eval (ρ.apply x) := by
  induction T with
  | leaf b => rfl
  | query i low high hl hh =>
    cases hρ : ρ i with
    | none =>
      cases hx : x i <;> simp [restrict, eval, PartialAssignment.apply, hρ, hx, hl, hh]
    | some b =>
      cases b <;> simp [restrict, eval, PartialAssignment.apply, hρ, hl, hh]

theorem restrict_depth_le {n : ℕ} (T : BooleanDecisionTree n)
    (ρ : PartialAssignment n) : (T.restrict ρ).depth ≤ T.depth := by
  induction T with
  | leaf b => exact le_rfl
  | query i low high hl hh =>
    cases hρ : ρ i with
    | none => simpa [restrict, hρ, depth] using Nat.add_le_add_right (max_le_max hl hh) 1
    | some b =>
      cases b
      · simpa only [restrict, hρ, depth] using
          hl.trans ((Nat.le_max_left _ _).trans (Nat.le_succ _))
      · simpa only [restrict, hρ, depth] using
          hh.trans ((Nat.le_max_right _ _).trans (Nat.le_succ _))

end BooleanDecisionTree

def HasSmallDecisionTree {n : ℕ} (f : BooleanCube n → Bool) (r : ℕ) : Prop :=
  ∃ T : BooleanDecisionTree n, T.depth ≤ r ∧ ∀ x, T.eval x = f x

theorem HasSmallDecisionTree.restrict {n r : ℕ} {f : BooleanCube n → Bool}
    (h : HasSmallDecisionTree f r) (ρ : PartialAssignment n) :
    HasSmallDecisionTree (fun x => f (ρ.apply x)) r := by
  obtain ⟨T, hT, he⟩ := h
  exact ⟨T.restrict ρ, (T.restrict_depth_le ρ).trans hT, fun x => by simp [he]⟩

theorem HasSmallDecisionTree.negate {n r : ℕ} {f : BooleanCube n → Bool}
    (h : HasSmallDecisionTree f r) : HasSmallDecisionTree (fun x => !(f x)) r := by
  obtain ⟨T, hT, he⟩ := h
  exact ⟨T.negate, by simpa using hT, fun x => by simp [he]⟩

@[simp] theorem hasSmallDecisionTree_negate_iff {n r : ℕ} {f : BooleanCube n → Bool} :
    HasSmallDecisionTree (fun x => !(f x)) r ↔ HasSmallDecisionTree f r := by
  constructor
  · intro h
    simpa only [Bool.not_not] using h.negate
  · exact HasSmallDecisionTree.negate

theorem literal_hasSmallDecisionTree {n r : ℕ} (i : Fin n) (b : Bool)
    (hr : 1 ≤ r) (ρ : PartialAssignment n) :
    HasSmallDecisionTree (fun x => (AC0Circuit.literal i b).eval (ρ.apply x)) r := by
  have h : HasSmallDecisionTree (AC0Circuit.literal i b).eval r := by
    refine ⟨.query i (.leaf (!b)) (.leaf b), ?_, ?_⟩
    · simpa [BooleanDecisionTree.depth] using hr
    · intro x
      cases b <;> cases hx : x i <;>
        simp [BooleanDecisionTree.eval, AC0Circuit.eval, hx]
  exact h.restrict ρ

end TwoPointCorrelations

end OAI
