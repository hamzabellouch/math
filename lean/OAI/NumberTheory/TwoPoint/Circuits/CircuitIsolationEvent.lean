import OAI.NumberTheory.TwoPoint.Circuits.CircuitBooleanOps
import OAI.NumberTheory.TwoPoint.Circuits.CircuitGateApproximation

namespace OAI

/-! The single-hit test used by the random polynomial is itself a small
constant-depth circuit on the original child outputs. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

namespace AC0Circuit

noncomputable def certificateDisjunction {ι : Type*} [Fintype ι] {n : ℕ}
    (c : ι → AC0Circuit n) : AC0Circuit n :=
  (conjunction (fun i => (c i).negate)).negate

lemma certificateDisjunction_eval {ι : Type*} [Fintype ι] {n : ℕ}
    (c : ι → AC0Circuit n) (x : BooleanCube n) :
    (certificateDisjunction c).eval x = true ↔ ∃ i, (c i).eval x = true := by
  rw [certificateDisjunction, negate_eval]
  simp only [ne_eq, conjunction_eval, negate_eval, not_forall, not_not]

lemma certificateDisjunction_depth {ι : Type*} [Fintype ι] {n d : ℕ}
    (c : ι → AC0Circuit n) (hc : ∀ i, (c i).depth ≤ d) :
    (certificateDisjunction c).depth ≤ d + 1 := by
  simp only [certificateDisjunction, negate_depth]
  exact conjunction_depth _ (fun i => by simpa only [negate_depth] using hc i)

lemma certificateDisjunction_size {ι : Type*} [Fintype ι] {n : ℕ}
    (c : ι → AC0Circuit n) : (certificateDisjunction c).size = 1 + ∑ i, (c i).size := by
  simp only [certificateDisjunction, negate_size, conjunction_size]

noncomputable def uniqueFalseTerm {n k : ℕ} (c : Fin k → AC0Circuit n)
    (S : Finset (Fin k)) (i : S) : AC0Circuit n :=
  conjunction (fun j : S => if j = i then (c j).negate else c j)

lemma uniqueFalseTerm_eval {n k : ℕ} (c : Fin k → AC0Circuit n)
    (S : Finset (Fin k)) (i : S) (x : BooleanCube n) :
    (uniqueFalseTerm c S i).eval x = true ↔
      (c i).eval x = false ∧ ∀ j : S, j ≠ i → (c j).eval x = true := by
  rw [uniqueFalseTerm, conjunction_eval]
  constructor
  · intro h
    refine ⟨?_, fun j hj => ?_⟩
    · have hi := h i
      apply Bool.eq_false_iff.mpr
      simpa only [ite_true, negate_eval] using hi
    · simpa only [ite_eq_right hj] using h j
  · rintro ⟨hi, h⟩ j
    by_cases hj : j = i
    · subst j
      rw [ite_eq_left rfl, negate_eval, hi]
      decide
    · simpa only [ite_eq_right hj] using h j hj

noncomputable def uniqueFalseCircuit {n k : ℕ} (c : Fin k → AC0Circuit n)
    (S : Finset (Fin k)) : AC0Circuit n :=
  certificateDisjunction (fun i : S => uniqueFalseTerm c S i)

lemma uniqueFalseCircuit_eval {n k : ℕ} (c : Fin k → AC0Circuit n)
    (S : Finset (Fin k)) (x : BooleanCube n) :
    (uniqueFalseCircuit c S).eval x = true ↔
      ∃ i : S, (c i).eval x = false ∧ ∀ j : S, j ≠ i → (c j).eval x = true := by
  simp only [uniqueFalseCircuit, certificateDisjunction_eval, uniqueFalseTerm_eval]

lemma uniqueFalseTerm_depth {n k d : ℕ} (c : Fin k → AC0Circuit n)
    (hc : ∀ i, (c i).depth ≤ d) (S : Finset (Fin k)) (i : S) :
    (uniqueFalseTerm c S i).depth ≤ d + 1 := by
  apply conjunction_depth
  intro j
  split_ifs <;> simpa only [negate_depth] using hc j

lemma uniqueFalseCircuit_depth {n k d : ℕ} (c : Fin k → AC0Circuit n)
    (hc : ∀ i, (c i).depth ≤ d) (S : Finset (Fin k)) :
    (uniqueFalseCircuit c S).depth ≤ d + 2 := by
  exact certificateDisjunction_depth _ (uniqueFalseTerm_depth c hc S)

lemma uniqueFalseTerm_size {n k : ℕ} (c : Fin k → AC0Circuit n)
    (S : Finset (Fin k)) (i : S) :
    (uniqueFalseTerm c S i).size = 1 + ∑ j : S, (c j).size := by
  rw [uniqueFalseTerm, conjunction_size]
  congr 1
  apply sum_congr rfl
  intro j _
  split_ifs <;> simp only [negate_size]

lemma uniqueFalseCircuit_size {n k : ℕ} (c : Fin k → AC0Circuit n)
    (S : Finset (Fin k)) :
    (uniqueFalseCircuit c S).size = 1 + S.card * (1 + ∑ j : S, (c j).size) := by
  simp only [uniqueFalseCircuit, certificateDisjunction_size, uniqueFalseTerm_size, sum_const,
    card_univ, Fintype.card_coe, nsmul_eq_mul, Nat.cast_id]

lemma uniqueFalseCircuit_size_le {n k : ℕ} (c : Fin k → AC0Circuit n)
    (S : Finset (Fin k)) :
    (uniqueFalseCircuit c S).size ≤ 1 + k * (1 + ∑ j, (c j).size) := by
  rw [uniqueFalseCircuit_size]
  have hcard : S.card ≤ k := (card_le_card (subset_univ S)).trans_eq (card_fin k)
  have hsum : ∑ j : S, (c j).size ≤ ∑ j, (c j).size := by
    calc
      _ = ∑ j ∈ S, (c j).size := sum_coe_sort S (fun j => (c j).size)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ S) (fun _ _ _ => Nat.zero_le _)
  exact Nat.add_le_add_left (Nat.mul_le_mul hcard (Nat.add_le_add_left hsum 1)) 1

end AC0Circuit

end TwoPointCorrelations

end OAI
