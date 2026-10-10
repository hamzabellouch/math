import OAI.Computability.UniqueGames.PCP.SourceAddressArithmeticLemmas
import OAI.Computability.UniqueGames.PCP.SourceTupleBody

namespace OAI

section

/-! Uniform polynomial bounds for the actual tuple-body phase budgets.
The budget being bounded is the one used by the checked machine traces. -/

namespace UniqueGamesTheorem.Foundations.Hastad.SourceTupleBound

open Complexity SourceContexts SourceOccurrences SourceTupleBody
open Complexity.MachineComposition

variable {u D : Nat}

theorem clauseRank_le_power (F : Target.Formula) (c : ClauseContext F u) :
    ((clauseEncoding F u).code c).val ≤ (formulaBits F).length ^ u := by
  have hr := ((clauseEncoding F u).code c).isLt
  change _ < F.clauses.length ^ u at hr
  exact hr.le.trans (Nat.pow_le_pow_left (SourceBounds.formulaBits_length_ge_clauses F) u)

theorem variableRank_le_power (F : Target.Formula) (c : ClauseContext F u)
    (index : Fin (SlotCount u)) :
    variableRank F c index ≤ (formulaBits F).length ^ u := by
  have hr := ((variableEncoding F u).code (sampledVariables F c (selected index))).isLt
  change variableRank F c index < F.variables ^ u at hr
  exact hr.le.trans (Nat.pow_le_pow_left (SourceBounds.formulaBits_length_ge_variables F) u)

theorem leftValue_le_numberBound (F : Target.Formula) (c : ClauseContext F u)
    (index : Fin (SlotCount u)) :
    leftValue F c index ≤ SourceBounds.bitCoefficient u * (formulaBits F).length ^ u :=
  (SourceAddressDescriptors.baseValue_lt F u c (sampledVariables F c (selected index)) 0).le.trans
    (SourceBounds.nBits_le_input F u)

theorem rightValue_le_numberBound (F : Target.Formula) (c : ClauseContext F u) :
    rightValue F c ≤ SourceBounds.bitCoefficient u * (formulaBits F).length ^ u :=
  (SourceAddressDescriptors.baseValue_lt F u c (sampledVariables F c (fun _ => .first)) 1).le.trans
    (SourceBounds.nBits_le_input F u)

theorem leftBlock_le_numberBound (F : Target.Formula) :
    2 ^ (2 ^ u) * F.variables ^ u ≤
      SourceBounds.bitCoefficient u * (formulaBits F).length ^ u := by
  apply Nat.le_trans (m := nBits F u)
  · rw [Nat.mul_comm (2 ^ (2 ^ u)) (F.variables ^ u), nBits_eq]
    omega
  · exact SourceBounds.nBits_le_input F u

noncomputable def rankPolynomial (u : Nat) : Polynomial Nat := Polynomial.X ^ u
noncomputable def numberPolynomial (u : Nat) : Polynomial Nat :=
  Polynomial.C (SourceBounds.bitCoefficient u) * Polynomial.X ^ u

@[simp] theorem rankPolynomial_eval (u L : Nat) : (rankPolynomial u).eval L = L ^ u := by
  simp [rankPolynomial]
@[simp] theorem numberPolynomial_eval (u L : Nat) :
    (numberPolynomial u).eval L = SourceBounds.bitCoefficient u * L ^ u := by
  simp [numberPolynomial]

noncomputable def slotPolynomial (u D : Nat) : Polynomial Nat :=
  Polynomial.C 1 + MachineHorner.timePolynomial u +
    (SourceBasePhase.timePolynomial (2 ^ (2 ^ u))).comp (rankPolynomial u + Polynomial.C 2) +
    (Polynomial.C (QueryCount u D) * (Polynomial.C 9 * numberPolynomial u + Polynomial.C 21) +
      Polynomial.C 1) +
    (rankPolynomial u + Polynomial.C 2) + (numberPolynomial u + Polynomial.C 2)

theorem slotPolynomial_eval (u D L : Nat) :
    (slotPolynomial u D).eval L =
      1 + (MachineHorner.timePolynomial u).eval L +
        (SourceBasePhase.timePolynomial (2 ^ (2 ^ u))).eval (L ^ u + 2) +
        (QueryCount u D * (9 * (SourceBounds.bitCoefficient u * L ^ u) + 21) + 1) +
        (L ^ u + 2) + (SourceBounds.bitCoefficient u * L ^ u + 2) := by
  simp only [slotPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_comp, rankPolynomial_eval, numberPolynomial_eval]

theorem slotBudget_le (F : Target.Formula) (c : ClauseContext F u)
    (index : Fin (SlotCount u)) :
    slotBudget (D := D) F c index ≤ (slotPolynomial u D).eval (formulaBits F).length := by
  have hr := variableRank_le_power F c index
  have hl := leftValue_le_numberBound F c index
  have hb := SourceBounds.nBits_le_input F u
  have hn := natPolynomial_eval_mono (MachineHorner.timePolynomial u)
    (SourceBounds.formulaBits_length_ge_variables F)
  have ho : SourceBasePhase.operandLength (variableRank F c index) 0 ≤
      (formulaBits F).length ^ u + 2 := by
    simp only [SourceBasePhase.operandLength, encodeWord_length]
    omega
  have ha := natPolynomial_eval_mono (SourceBasePhase.timePolynomial (2 ^ (2 ^ u))) ho
  have hq := Nat.mul_le_mul_left (QueryCount u D)
    (Nat.add_le_add_right (Nat.mul_le_mul_left 9 hb) 21)
  rw [slotPolynomial_eval]
  unfold slotBudget
  omega

theorem prefixBudget_le (F : Target.Formula) (c : ClauseContext F u) (r : Nat) :
    prefixBudget (D := D) F c r ≤ r * (slotPolynomial u D).eval (formulaBits F).length := by
  induction r with
  | zero => simp [prefixBudget]
  | succ r ih =>
    rw [prefixBudget]
    split
    next h =>
      have hs := slotBudget_le (D := D) F c ⟨r, h⟩
      simpa only [Nat.succ_mul] using Nat.add_le_add ih hs
    next _ =>
      simpa only [Nat.add_zero] using ih.trans
        (Nat.mul_le_mul_right ((slotPolynomial u D).eval (formulaBits F).length) (Nat.le_succ r))

noncomputable def preparePolynomial (u : Nat) : Polynomial Nat :=
  Polynomial.C u * (Polynomial.C 10 * Polynomial.X + Polynomial.C 20) + Polynomial.C 1 +
    (Polynomial.C (SourceSignaturePrepare.Width u * SourceSignaturePrepare.Width u) *
      (Polynomial.C 5 * Polynomial.X + Polynomial.C 6) + Polynomial.C 2)

theorem preparePolynomial_eval (u L : Nat) :
    (preparePolynomial u).eval L =
      (u * (10 * L + 20) + 1) +
        (SourceSignaturePrepare.Width u * SourceSignaturePrepare.Width u * (5 * L + 6) + 2) := by
  simp only [preparePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]

noncomputable def setupPolynomial (u : Nat) : Polynomial Nat :=
  preparePolynomial u + Polynomial.C 1 + MachineHorner.timePolynomial u +
    (SourceBasePhase.timePolynomial (2 ^ (8 ^ u))).comp
      (rankPolynomial u + numberPolynomial u + Polynomial.C 2) +
    (rankPolynomial u + Polynomial.C 2)

theorem setupPolynomial_eval (u L : Nat) :
    (setupPolynomial u).eval L =
      (preparePolynomial u).eval L + 1 + (MachineHorner.timePolynomial u).eval L +
        (SourceBasePhase.timePolynomial (2 ^ (8 ^ u))).eval
          (L ^ u + SourceBounds.bitCoefficient u * L ^ u + 2) + (L ^ u + 2) := by
  simp only [setupPolynomial, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_comp, rankPolynomial_eval, numberPolynomial_eval]

noncomputable def finishPolynomial (u : Nat) : Polynomial Nat :=
  Polynomial.C 1 + (numberPolynomial u + Polynomial.C 2) + Polynomial.C 2 +
    (Polynomial.C (6 * u) * (Polynomial.X + Polynomial.C 1) + Polynomial.C 1) + Polynomial.C 1

theorem finishPolynomial_eval (u L : Nat) :
    (finishPolynomial u).eval L =
      1 + (SourceBounds.bitCoefficient u * L ^ u + 2) + 2 + (6 * u * (L + 1) + 1) + 1 := by
  simp only [finishPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, numberPolynomial_eval]

noncomputable def bodyPolynomial (u D : Nat) : Polynomial Nat :=
  setupPolynomial u + Polynomial.C (SlotCount u) * slotPolynomial u D + finishPolynomial u

theorem setupBudget_le (F : Target.Formula) (c : ClauseContext F u) :
    setupBudget F c ≤ (setupPolynomial u).eval (formulaBits F).length := by
  have hr := clauseRank_le_power F c
  have hl := leftBlock_le_numberBound (u := u) F
  have hm := natPolynomial_eval_mono (MachineHorner.timePolynomial u)
    (SourceBounds.formulaBits_length_ge_clauses F)
  have ho : SourceBasePhase.operandLength (((clauseEncoding F u).code c).val)
      (2 ^ (2 ^ u) * F.variables ^ u) ≤
      (formulaBits F).length ^ u +
        SourceBounds.bitCoefficient u * (formulaBits F).length ^ u + 2 := by
    simp only [SourceBasePhase.operandLength, encodeWord_length]
    omega
  have ha := natPolynomial_eval_mono (SourceBasePhase.timePolynomial (2 ^ (8 ^ u))) ho
  rw [setupPolynomial_eval, preparePolynomial_eval]
  unfold setupBudget
  omega

theorem finishBudget_le (F : Target.Formula) (c : ClauseContext F u) :
    finishBudget F c ≤ (finishPolynomial u).eval (formulaBits F).length := by
  have hr := rightValue_le_numberBound F c
  rw [finishPolynomial_eval]
  unfold finishBudget
  omega

/-- One fixed polynomial bounds the actual tuple-body budget for every tuple. -/
theorem bodyBudget_le (F : Target.Formula) (c : ClauseContext F u) :
    bodyBudget (D := D) F c ≤ (bodyPolynomial u D).eval (formulaBits F).length := by
  have hs := setupBudget_le F c
  have hp := prefixBudget_le (D := D) F c (SlotCount u)
  have hf := finishBudget_le F c
  simp only [bodyPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  unfold bodyBudget
  omega

theorem fixed_parameters_body_bound (u D : Nat) :
    ∃ p : Polynomial Nat, ∀ (F : Target.Formula) (c : ClauseContext F u),
      bodyBudget (D := D) F c ≤ p.eval (formulaBits F).length :=
  ⟨bodyPolynomial u D, fun F c => bodyBudget_le F c⟩

/-- The actual body execution with the same fixed polynomial for every tuple. -/
theorem bodyInPolynomialTime {Extra : Type} [DecidableEq Extra]
    (F : Target.Formula) (c : ClauseContext F u)
    (initialQuery : Query u D) (exit : Option (Label u D Extra))
    (base : SourceRuntimeModel.Arena u Extra → List Bool) (h : Ready F c base) :
    Nonempty (StateTransition.EvalsToInTime (Turing.TM2.step (program initialQuery exit))
      ⟨some main, SourceRuntimeModel.canonicalState initialQuery, base⟩
      (some ⟨exit, SourceRuntimeModel.canonicalState initialQuery,
        SourceTestAppend.resultTapes SourceRuntimeModel.queryLayout base
          (SourceQueryOrder.tupleBits F u D c)⟩)
      ((bodyPolynomial u D).eval (formulaBits F).length)) := by
  obtain ⟨run⟩ := bodyInTime F c initialQuery exit base h
  exact ⟨{
    toEvalsTo := run.toEvalsTo
    steps_le_m := run.steps_le_m.trans (bodyBudget_le F c)
  }⟩

end UniqueGamesTheorem.Foundations.Hastad.SourceTupleBound

end

end OAI
