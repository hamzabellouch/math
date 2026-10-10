import OAI.NumberTheory.TwoPoint.Circuits.CircuitCanonicalTree

namespace OAI

/-! A decision tree of depth r is a DNF of width at most r. Both Boolean
polarities have such a representation, so gates can be switched without
counting the number of clauses produced by earlier switches. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

namespace BooleanDecisionTree

def negate {n : ℕ} : BooleanDecisionTree n → BooleanDecisionTree n
  | .leaf b => .leaf (!b)
  | .query i low high => .query i low.negate high.negate

@[simp] lemma negate_eval {n : ℕ} (T : BooleanDecisionTree n) (x : BooleanCube n) :
    T.negate.eval x = !(T.eval x) := by
  induction T with
  | leaf b => rfl
  | query i low high hl hh =>
    cases hx : x i <;> simp [negate, eval, hx, hl, hh]

@[simp] lemma negate_depth {n : ℕ} (T : BooleanDecisionTree n) : T.negate.depth = T.depth := by
  induction T with
  | leaf b => rfl
  | query i low high hl hh => simp [negate, depth, hl, hh]

end BooleanDecisionTree

def CubeTerm.withLiteral {n : ℕ} (C : CubeTerm n) (i : Fin n) (b : Bool) : CubeTerm n :=
  ⟨insert i C.support, Function.update C.value i b⟩

lemma CubeTerm.withLiteral_eval {n : ℕ} (C : CubeTerm n) (i : Fin n) (b : Bool)
    (hc : i ∉ C.support ∨ C.value i = b) (x : BooleanCube n) :
    (C.withLiteral i b).eval x = true ↔ x i = b ∧ C.eval x = true := by
  simp only [eval, decide_eq_true_eq]
  constructor
  · intro h
    have hi := h i (mem_insert_self _ _)
    have hx : x i = b := by simpa [withLiteral] using hi
    refine ⟨hx, ?_⟩
    intro j hj
    by_cases hji : j = i
    · subst j
      exact hx.trans ((hc.resolve_left (not_not.mpr hj)).symm)
    · have hh := h j (mem_insert_of_mem hj)
      simpa [withLiteral, hji] using hh
  · rintro ⟨hi, h⟩ j hj
    rcases mem_insert.mp hj with rfl | hj
    · simpa [withLiteral] using hi
    · by_cases hji : j = i
      · subst j
        simpa [withLiteral] using hi
      · simpa [withLiteral, hji] using h j hj

def addDNFLiteral {n : ℕ} (F : List (CubeTerm n)) (i : Fin n) (b : Bool) :
    List (CubeTerm n) :=
  F.flatMap (fun C => if i ∉ C.support ∨ C.value i = b then [C.withLiteral i b] else [])

lemma dnfEval_eq_true {n : ℕ} (F : List (CubeTerm n)) (x : BooleanCube n) :
    dnfEval F x = true ↔ ∃ C ∈ F, C.eval x = true := by
  simp [dnfEval]

lemma addDNFLiteral_eval {n : ℕ} (F : List (CubeTerm n)) (i : Fin n) (b : Bool)
    (x : BooleanCube n) :
    dnfEval (addDNFLiteral F i b) x = true ↔ x i = b ∧ dnfEval F x = true := by
  simp only [dnfEval_eq_true, addDNFLiteral, List.mem_flatMap]
  constructor
  · rintro ⟨D, ⟨C, hC, hD⟩, he⟩
    split_ifs at hD with hc
    · have hDC : D = C.withLiteral i b := by simpa using hD
      subst D
      have hh := (C.withLiteral_eval i b hc x).mp he
      exact ⟨hh.1, C, hC, hh.2⟩
    · simp at hD
  · rintro ⟨hxi, C, hC, he⟩
    have hc : i ∉ C.support ∨ C.value i = b := by
      by_cases hi : i ∈ C.support
      · right
        have hh := (of_decide_eq_true he) i hi
        exact hh.symm.trans hxi
      · exact Or.inl hi
    refine ⟨C.withLiteral i b, ⟨C, hC, ?_⟩, (C.withLiteral_eval i b hc x).mpr ⟨hxi, he⟩⟩
    simp [hc]

lemma addDNFLiteral_width {n r : ℕ} (F : List (CubeTerm n))
    (hF : ∀ C ∈ F, C.support.card ≤ r) (i : Fin n) (b : Bool) :
    ∀ C ∈ addDNFLiteral F i b, C.support.card ≤ r + 1 := by
  intro D hD
  obtain ⟨C, hC, hD⟩ := List.mem_flatMap.mp hD
  split_ifs at hD with hc
  · have hDC : D = C.withLiteral i b := by simpa using hD
    subst D
    exact (card_insert_le i C.support).trans (Nat.add_le_add_right (hF C hC) 1)
  · simp at hD

namespace BooleanDecisionTree

def toDNF {n : ℕ} : BooleanDecisionTree n → List (CubeTerm n)
  | .leaf false => []
  | .leaf true => [⟨∅, fun _ => false⟩]
  | .query i low high => addDNFLiteral low.toDNF i false ++ addDNFLiteral high.toDNF i true

theorem toDNF_eval {n : ℕ} (T : BooleanDecisionTree n) (x : BooleanCube n) :
    dnfEval T.toDNF x = T.eval x := by
  apply Bool.eq_iff_iff.mpr
  induction T with
  | leaf b => cases b <;> simp [toDNF, dnfEval, eval, CubeTerm.eval]
  | query i low high hl hh =>
    simp only [toDNF, dnfEval, List.any_append, Bool.or_eq_true]
    change (dnfEval (addDNFLiteral low.toDNF i false) x = true ∨
      dnfEval (addDNFLiteral high.toDNF i true) x = true) ↔ _
    rw [addDNFLiteral_eval, addDNFLiteral_eval, hl, hh]
    cases hx : x i <;> simp [eval, hx]

theorem toDNF_width {n : ℕ} (T : BooleanDecisionTree n) :
    ∀ C ∈ T.toDNF, C.support.card ≤ T.depth := by
  induction T with
  | leaf b => cases b <;> simp [toDNF, depth]
  | query i low high hl hh =>
    intro C hC
    rcases List.mem_append.mp hC with hC | hC
    · exact (addDNFLiteral_width low.toDNF hl i false C hC).trans
        (Nat.add_le_add_right (Nat.le_max_left _ _) 1)
    · exact (addDNFLiteral_width high.toDNF hh i true C hC).trans
        (Nat.add_le_add_right (Nat.le_max_right _ _) 1)

end BooleanDecisionTree

end TwoPointCorrelations

end OAI
