import OAI.NumberTheory.TwoPoint.Circuits.CircuitBooleanOps
import OAI.NumberTheory.TwoPoint.Bounds.ActiveStateVectors

namespace OAI

/-! Exact signed state expansion for a closed word. The padding states
are truncated; every centered-prime bit is retained. The remaining
predicate is a circuit, including all prohibited-vertex tests. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def weightedStateCircuit {R n t m : ℕ}
    (qindex : Fin R → Fin n → Fin m) (pindex : Fin t → Fin m)
    (S : Fin R → Finset (Fin n)) (bits : BooleanCube t) (c : AC0Circuit m) :
    AC0Circuit m :=
  AC0Circuit.conjunction (fun i : Fin 3 =>
    ![activeStateVectorCircuit qindex S, AC0Circuit.assignmentTerm pindex bits, c] i)

lemma weightedStateCircuit_eval {R n t m : ℕ}
    (qindex : Fin R → Fin n → Fin m) (pindex : Fin t → Fin m)
    (S : Fin R → Finset (Fin n)) (bits : BooleanCube t) (c : AC0Circuit m)
    (x : BooleanCube m) :
    (weightedStateCircuit qindex pindex S bits c).eval x = true ↔
      (∀ r, activeState (fun i => x (qindex r i)) = S r) ∧
      (fun i => x (pindex i)) = bits ∧ c.eval x = true := by
  simp only [weightedStateCircuit, AC0Circuit.conjunction_eval, Fin.forall_fin_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ,
    activeStateVectorCircuit_eval, AC0Circuit.assignmentTerm_eval_true]
  simp

lemma weightedStateCircuit_depth {R n t m : ℕ}
    (qindex : Fin R → Fin n → Fin m) (pindex : Fin t → Fin m)
    (S : Fin R → Finset (Fin n)) (bits : BooleanCube t) (c : AC0Circuit m)
    (hc : c.depth ≤ 19) :
    (weightedStateCircuit qindex pindex S bits c).depth ≤ 20 := by
  apply AC0Circuit.conjunction_depth (d := 19)
  intro i
  fin_cases i
  · exact (activeStateVectorCircuit_depth qindex S).trans (by norm_num)
  · simp [AC0Circuit.assignmentTerm_depth]
  · exact hc

lemma weightedStateCircuit_size {R n t m : ℕ}
    (qindex : Fin R → Fin n → Fin m) (pindex : Fin t → Fin m)
    (S : Fin R → Finset (Fin n)) (bits : BooleanCube t) (c : AC0Circuit m) :
    (weightedStateCircuit qindex pindex S bits c).size =
      3 + R * (1 + n) + t + c.size := by
  simp [weightedStateCircuit, AC0Circuit.conjunction_size, Fin.sum_univ_succ,
    activeStateVectorCircuit_size, AC0Circuit.assignmentTerm_size]
  omega

theorem weightedWord_scalar_expansion {R n t m : ℕ} (M : ℕ)
    (qindex : Fin R → Fin n → Fin m) (pindex : Fin t → Fin m)
    (f : (Fin R → Finset (Fin n)) → BooleanCube t → ℝ)
    (c : AC0Circuit m) (x : BooleanCube m) :
    (if (∀ r, (activeState (fun i => x (qindex r i))).card ≤ M) ∧ c.eval x = true
      then f (fun r => activeState (fun i => x (qindex r i))) (fun i => x (pindex i))
      else 0) =
    ∑ b : (Fin R → boundedActiveStates n M) × BooleanCube t,
      f (fun r => (b.1 r).val) b.2 *
        (weightedStateCircuit qindex pindex (fun r => (b.1 r).val) b.2 c).indicator x := by
  by_cases hx : (∀ r, (activeState (fun i => x (qindex r i))).card ≤ M) ∧ c.eval x = true
  · let b₀ : (Fin R → boundedActiveStates n M) × BooleanCube t :=
      (fun r => ⟨activeState (fun i => x (qindex r i)), mem_boundedActiveStates.mpr (hx.1 r)⟩,
        fun i => x (pindex i))
    rw [ite_eq_left hx, sum_eq_single b₀]
    · have he := (weightedStateCircuit_eval qindex pindex
        (fun r => (b₀.1 r).val) b₀.2 c x).mpr ⟨fun _ => rfl, rfl, hx.2⟩
      simp only [AC0Circuit.indicator, he, ite_true, mul_one]
      rfl
    · intro b _ hb
      have he : (weightedStateCircuit qindex pindex
          (fun r => (b.1 r).val) b.2 c).eval x ≠ true := by
        intro he
        obtain ⟨hS, hp, _⟩ := (weightedStateCircuit_eval qindex pindex _ _ c x).mp he
        apply hb
        apply Prod.ext
        · funext r
          exact Subtype.ext (hS r).symm
        · exact hp.symm
      simp [AC0Circuit.indicator, he]
    · simp
  · rw [ite_eq_right hx]
    symm
    apply sum_eq_zero
    intro b _
    have he : (weightedStateCircuit qindex pindex
        (fun r => (b.1 r).val) b.2 c).eval x ≠ true := by
      intro he
      obtain ⟨hS, _, hc⟩ := (weightedStateCircuit_eval qindex pindex _ _ c x).mp he
      apply hx
      refine ⟨?_, hc⟩
      intro r
      rw [hS r]
      exact mem_boundedActiveStates.mp (b.1 r).property
    simp [AC0Circuit.indicator, he]

lemma weightedWord_coefficient_mass {R n t M : ℕ}
    (f : (Fin R → Finset (Fin n)) → BooleanCube t → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ b : (Fin R → boundedActiveStates n M) × BooleanCube t,
      |f (fun r => (b.1 r).val) b.2| ≤ C) :
    (∑ b : (Fin R → boundedActiveStates n M) × BooleanCube t,
      |f (fun r => (b.1 r).val) b.2|) ≤
        (((M + 1) * (n + 1) ^ M : ℕ) : ℝ) ^ R * (2 : ℝ) ^ t * C := by
  calc
    _ ≤ ∑ _b : (Fin R → boundedActiveStates n M) × BooleanCube t, C :=
      sum_le_sum (fun b _ => hf b)
    _ = ((boundedActiveStates n M).card : ℝ) ^ R * (2 : ℝ) ^ t * C := by
      simp [BooleanCube, Fintype.card_prod, Nat.cast_mul, Nat.cast_pow]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) (by exact_mod_cast boundedActiveStates_card n M) R)
        (by positivity)) hC

end TwoPointCorrelations

end OAI
