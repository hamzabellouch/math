import OAI.NumberTheory.TwoPoint.Bounds.ActiveStateBudget

namespace OAI

/-! Simultaneous bounded active states at every vertex of a trace word.
Offsets may share residue coordinates; the circuit keeps this sharing explicit. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

def activeStateVectorCircuit {R n m : ℕ} (index : Fin R → Fin n → Fin m)
    (S : Fin R → Finset (Fin n)) : AC0Circuit m :=
  .andGate (fun r => .andGate (fun i => .literal (index r i) (decide (i ∈ S r))))

lemma activeStateVectorCircuit_eval {R n m : ℕ} (index : Fin R → Fin n → Fin m)
    (S : Fin R → Finset (Fin n)) (x : BooleanCube m) :
    (activeStateVectorCircuit index S).eval x = true ↔
      ∀ r, activeState (fun i => x (index r i)) = S r := by
  change (decide (∀ r, (activeStateCircuit (S r)).eval (fun i => x (index r i)) = true) = true) ↔ _
  simp only [decide_eq_true_eq, activeStateCircuit_eval]

lemma activeStateVectorCircuit_depth {R n m : ℕ} (index : Fin R → Fin n → Fin m)
    (S : Fin R → Finset (Fin n)) : (activeStateVectorCircuit index S).depth ≤ 2 := by
  change 1 + (univ.sup fun r : Fin R => (activeStateCircuit (S r)).depth) ≤ 2
  have hh : (univ.sup fun r : Fin R => (activeStateCircuit (S r)).depth) ≤ 1 :=
    Finset.sup_le (fun r _ => activeStateCircuit_depth (S r))
  omega

lemma activeStateVectorCircuit_size {R n m : ℕ} (index : Fin R → Fin n → Fin m)
    (S : Fin R → Finset (Fin n)) :
    (activeStateVectorCircuit index S).size = 1 + R * (1 + n) := by
  simp [activeStateVectorCircuit, AC0Circuit.size]

theorem activeStateVector_scalar_expansion {R n m : ℕ} (M : ℕ)
    (index : Fin R → Fin n → Fin m) (f : (Fin R → Finset (Fin n)) → ℝ)
    (x : BooleanCube m) :
    (if ∀ r, (activeState (fun i => x (index r i))).card ≤ M
      then f (fun r => activeState (fun i => x (index r i))) else 0) =
      ∑ b : Fin R → boundedActiveStates n M,
        f (fun r => (b r).val) *
          (activeStateVectorCircuit index (fun r => (b r).val)).indicator x := by
  by_cases hx : ∀ r, (activeState (fun i => x (index r i))).card ≤ M
  · let b₀ : Fin R → boundedActiveStates n M := fun r =>
      ⟨activeState (fun i => x (index r i)), mem_boundedActiveStates.mpr (hx r)⟩
    rw [ite_eq_left hx, sum_eq_single b₀]
    · have he : (activeStateVectorCircuit index (fun r => (b₀ r).val)).eval x = true :=
        (activeStateVectorCircuit_eval index _ x).mpr (fun _ => rfl)
      simp only [AC0Circuit.indicator, he, ite_true, mul_one]
      rfl
    · intro b _ hb
      have he : (activeStateVectorCircuit index (fun r => (b r).val)).eval x ≠ true := by
        intro he
        have hs := (activeStateVectorCircuit_eval index _ x).mp he
        apply hb
        funext r
        exact Subtype.ext (hs r).symm
      simp [AC0Circuit.indicator, he]
    · simp
  · rw [ite_eq_right hx]
    symm
    apply sum_eq_zero
    intro b _
    have he : (activeStateVectorCircuit index (fun r => (b r).val)).eval x ≠ true := by
      intro he
      have hs := (activeStateVectorCircuit_eval index _ x).mp he
      apply hx
      intro r
      rw [hs r]
      exact mem_boundedActiveStates.mp (b r).property
    simp [AC0Circuit.indicator, he]

lemma activeStateVector_coefficient_mass {R n M : ℕ}
    (f : (Fin R → Finset (Fin n)) → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ b : Fin R → boundedActiveStates n M, |f (fun r => (b r).val)| ≤ C) :
    (∑ b : Fin R → boundedActiveStates n M, |f (fun r => (b r).val)|) ≤
      (((M + 1) * (n + 1) ^ M : ℕ) : ℝ) ^ R * C := by
  calc
    _ ≤ ∑ _b : Fin R → boundedActiveStates n M, C := sum_le_sum (fun b _ => hf b)
    _ = ((boundedActiveStates n M).card : ℝ) ^ R * C := by
      simp only [sum_const, card_univ, Fintype.card_fun, Fintype.card_coe, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_pow]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) (by exact_mod_cast boundedActiveStates_card n M) R) hC

lemma activeStateVector_size_budget {R n m : ℕ} (L : ℝ)
    (index : Fin R → Fin n → Fin m) (S : Fin R → Finset (Fin n))
    (hL : 8 ≤ L) (hn : (n : ℝ) ≤ Real.exp L) (hR : (R : ℝ) ≤ 4 * L) :
    ((activeStateVectorCircuit index S).size : ℝ) ≤ Real.exp (L ^ 6) := by
  rw [activeStateVectorCircuit_size]
  push_cast
  have hE : (9 : ℝ) ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have hEL : L ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have hE1 : (1 : ℝ) ≤ Real.exp L := by linarith
  have hprod := mul_le_mul hR (show (1 : ℝ) + n ≤ 2 * Real.exp L by linarith)
    (show (0 : ℝ) ≤ 1 + n by positivity) (show 0 ≤ 4 * L by linarith)
  have h2 : Real.exp (2 * L) = Real.exp L * Real.exp L := by
    rw [show 2 * L = L + L by ring, Real.exp_add]
  have h3 : Real.exp (3 * L) = Real.exp L * Real.exp (2 * L) := by
    rw [show 3 * L = L + 2 * L by ring, Real.exp_add]
  have h26 : L ^ 2 ≤ L ^ 6 := pow_le_pow_right₀ (by linarith : 1 ≤ L) (by norm_num)
  calc
    _ ≤ 9 * Real.exp (2 * L) := by rw [h2]; nlinarith
    _ ≤ Real.exp (3 * L) := by rw [h3]; exact mul_le_mul_of_nonneg_right hE (Real.exp_pos _).le
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

lemma activeStateVector_coefficient_budget {R n M : ℕ} (L : ℝ)
    (f : (Fin R → Finset (Fin n)) → ℝ)
    (hL : 4800 ≤ L) (hn : (n : ℝ) ≤ Real.exp L)
    (hM : (M : ℝ) ≤ 400 * Real.log L) (hR : (R : ℝ) ≤ 4 * L)
    (hf : ∀ b : Fin R → boundedActiveStates n M,
      |f (fun r => (b r).val)| ≤ Real.exp (L ^ 4)) :
    (∑ b : Fin R → boundedActiveStates n M, |f (fun r => (b r).val)|) ≤
      Real.exp (L ^ 5) := by
  apply (activeStateVector_coefficient_mass f (Real.exp (L ^ 4)) (Real.exp_pos _).le hf).trans
  calc
    _ ≤ Real.exp (L ^ 4) * Real.exp (L ^ 4) :=
      mul_le_mul_of_nonneg_right (active_state_family_cost L n M R hL hn hM hR) (Real.exp_pos _).le
    _ = Real.exp (2 * L ^ 4) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have ht := mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ L by linarith)
        (pow_nonneg (show 0 ≤ L by linarith) 4)
      calc
        2 * L ^ 4 ≤ L * L ^ 4 := ht
        _ = L ^ 5 := by ring

end TwoPointCorrelations

end OAI
