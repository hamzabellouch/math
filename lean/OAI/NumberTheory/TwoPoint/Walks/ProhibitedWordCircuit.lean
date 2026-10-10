import OAI.NumberTheory.TwoPoint.Walks.ProhibitedCircuitBounds
import OAI.NumberTheory.TwoPoint.Circuits.CircuitBooleanOps
import OAI.NumberTheory.TwoPoint.Walks.ProhibitedDensity
import OAI.NumberTheory.TwoPoint.Bounds.PrimeLiteralEncoding

namespace OAI

/-! The surviving-site mask for every departure of one closed word is
an actual small circuit. Each complemented prohibited DNF keeps its
original prime input occurrences. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def prohibitedWordKeepCircuit (pairs : Finset (ℕ × ℕ)) (h s : ℕ)
    {R n : ℕ} (index : Fin R → Fin (Fintype.card (ProhibitedInputs pairs h s)) → Fin n) :
    AC0Circuit n :=
  AC0Circuit.conjunction (fun r => ((prohibitedCircuit pairs h s).negate).relabel (index r))

lemma prohibitedWordKeepCircuit_eval (pairs : Finset (ℕ × ℕ)) (h s : ℕ)
    (hsq : ∀ dq ∈ pairs, Squarefree (dq.2 * dq.1))
    {R n : ℕ} (index : Fin R → Fin (Fintype.card (ProhibitedInputs pairs h s)) → Fin n)
    (site : Fin R → ℤ) (x : BooleanCube n)
    (hx : ∀ r i, x (index r i) = prohibitedInputAt pairs h s (site r) i) :
    (prohibitedWordKeepCircuit pairs h s index).eval x = true ↔
      ∀ r, ¬ProhibitedSite h s (fun d q => (d, q) ∈ pairs) (site r) := by
  rw [prohibitedWordKeepCircuit, AC0Circuit.conjunction_eval]
  apply forall_congr'
  intro r
  rw [AC0Circuit.relabel_eval, AC0Circuit.negate_eval]
  have hb : (fun i => x (index r i)) = prohibitedInputAt pairs h s (site r) := funext (hx r)
  rw [hb, ne_eq, prohibitedCircuit_correct pairs h s (site r) hsq]

lemma prohibitedWordKeepCircuit_depth (pairs : Finset (ℕ × ℕ)) (h s : ℕ)
    {R n : ℕ} (index : Fin R → Fin (Fintype.card (ProhibitedInputs pairs h s)) → Fin n) :
    (prohibitedWordKeepCircuit pairs h s index).depth ≤ 3 := by
  apply AC0Circuit.conjunction_depth (d := 2)
  intro r
  exact (AC0Circuit.relabel_depth _ _).trans
    ((AC0Circuit.negate_depth _).le.trans (prohibitedCircuit_depth pairs h s))

lemma prohibitedWordKeepCircuit_size (pairs : Finset (ℕ × ℕ)) (h s : ℕ)
    {R n : ℕ} (index : Fin R → Fin (Fintype.card (ProhibitedInputs pairs h s)) → Fin n) :
    (prohibitedWordKeepCircuit pairs h s index).size ≤
      1 + R * (prohibitedCircuit pairs h s).size := by
  rw [prohibitedWordKeepCircuit, AC0Circuit.conjunction_size]
  apply Nat.add_le_add_left
  calc
    _ ≤ ∑ _r : Fin R, (prohibitedCircuit pairs h s).size := by
      apply sum_le_sum
      intro r _
      exact (AC0Circuit.relabel_size _ _).trans (AC0Circuit.negate_size _).le
    _ = _ := by simp

lemma prohibitedWordKeepCircuit_size_budget (pairs : Finset (ℕ × ℕ)) (h s M : ℕ)
    {R n : ℕ} (index : Fin R → Fin (Fintype.card (ProhibitedInputs pairs h s)) → Fin n)
    (L : ℝ) (hL : 110 ≤ L) (hR : (R : ℝ) ≤ 4 * L) (hs : (s : ℝ) ≤ L)
    (hM : (M : ℝ) ≤ L ^ 2) (hpairs : (pairs.card : ℝ) ≤ Real.exp (101 * L))
    (hcap : ∀ dq ∈ pairs, (dq.2 * dq.1).primeFactors.card ≤ M) :
    ((prohibitedWordKeepCircuit pairs h s index).size : ℝ) ≤ Real.exp (L ^ 3) := by
  have hb := prohibitedCircuit_size_quadratic pairs h s M L hL hs hM hpairs hcap
  have hn : (0 : ℝ) ≤ (prohibitedCircuit pairs h s).size := Nat.cast_nonneg _
  have hraw : ((prohibitedWordKeepCircuit pairs h s index).size : ℝ) ≤
      1 + R * (prohibitedCircuit pairs h s).size := by
    exact_mod_cast prohibitedWordKeepCircuit_size pairs h s index
  have hE : (1 : ℝ) ≤ Real.exp (104 * L ^ 2) := Real.one_le_exp_iff.mpr (by positivity)
  have hLexp : L ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have h5 : (5 : ℝ) ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have hLp : 0 ≤ L := by linarith
  calc
    _ ≤ 1 + 4 * L * Real.exp (104 * L ^ 2) := by
      apply hraw.trans
      gcongr
    _ ≤ 5 * Real.exp L * Real.exp (104 * L ^ 2) := by nlinarith [Real.exp_pos L]
    _ ≤ Real.exp L * Real.exp L * Real.exp (104 * L ^ 2) := by gcongr
    _ = Real.exp (104 * L ^ 2 + 2 * L) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (105 * L ^ 2) := Real.exp_le_exp.mpr (by nlinarith)
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (show 0 ≤ L - 105 by linarith) (sq_nonneg L)]

/-- Every literal in the numerical prohibited-word DNF uses a prime in
its actual tuple-or-padding pool. -/
lemma ProhibitedPrimeFamily.prohibited_input_mem {h J M : ℕ}
    (data : ProhibitedPrimeFamily h J M) (s : ℕ)
    (i : ProhibitedInputs data.pairs h s) : i.2.2.val ∈ data.P ∪ data.Q := by
  apply data.support_subset s i.1
  apply mem_biUnion.mpr
  refine ⟨(decodeStepWord i.1.val).get i.2.1, ?_, i.2.2.property⟩
  exact List.mem_toFinset.mpr (List.get_mem _ _)

noncomputable def ProhibitedPrimeFamily.prohibitedLiteral {h J M : ℕ}
    (data : ProhibitedPrimeFamily h J M) (s : ℕ)
    (i : Fin (Fintype.card (ProhibitedInputs data.pairs h s))) :
    ↥(data.P ∪ data.Q) × ℤ :=
  let v := (prohibitedInputIndex data.pairs h s).symm i
  (⟨v.2.2.val, data.prohibited_input_mem s v⟩,
    wordDisplacement h ((decodeStepWord v.1.val).take v.2.1.val))

lemma ProhibitedPrimeFamily.prohibitedLiteral_integer_input {h J M : ℕ}
    (data : ProhibitedPrimeFamily h J M) (s : ℕ) (a : ℤ)
    (i : Fin (Fintype.card (ProhibitedInputs data.pairs h s))) :
    residueCircuitInputs (primeResidueModuli (data.P ∪ data.Q))
      (primeLiteralCoordinate (data.P ∪ data.Q) (data.prohibitedLiteral s))
      (primeLiteralTest (data.P ∪ data.Q) (data.prohibitedLiteral s))
      (fun j => (a : ZMod (primeResidueModuli (data.P ∪ data.Q) j))) i =
      prohibitedInputAt data.pairs h s a i := by
  rw [primeLiteral_integer_input]
  rfl

end TwoPointCorrelations

end OAI
