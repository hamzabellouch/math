import OAI.Computability.BinPacking.CookLevin.ConfigIndex

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.MachineCircuit

open Turing StatementCircuit BoundedExecution
open scoped BigOperators

variable {K : Type} {Γ : K → Type} {Λ σ : Type}
variable [DecidableEq K] [Fintype Λ] [DecidableEq Λ]
variable [Fintype σ] [DecidableEq σ]
variable [∀ k, Fintype (Γ k)] [∀ k, DecidableEq (Γ k)]

private theorem bool_ext {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

def StepSafe (S : Nat) (program : Λ → TM2.Stmt Γ Λ σ) (cfg : TM2.Cfg Γ Λ σ) : Prop :=
  ∀ label, cfg.l = some label → StatementSafe S (program label) cfg.var cfg.stk

noncomputable def liveCase (S : Nat) (program : Λ → TM2.Stmt Γ Λ σ)
    (bit : ConfigBit Γ Λ σ S) (label : Λ) : Expr (ConfigBit Γ Λ σ S) :=
  .and (.input (.inl (some label)))
    ((transitionExpr S (program label) bit).rename Sum.inr)

noncomputable def stickyExpr (S : Nat) (program : Λ → TM2.Stmt Γ Λ σ)
    (bit : ConfigBit Γ Λ σ S) : Expr (ConfigBit Γ Λ σ S) :=
  .or (.and (.input (.inl none)) (.input bit))
    (Expr.disjoin (Finset.univ.toList.map (liveCase S program bit)))

omit [Fintype Λ] [DecidableEq Λ] [Fintype σ] [DecidableEq σ]
  [∀ stack, Fintype (Γ stack)] [∀ stack, DecidableEq (Γ stack)] in
theorem absorbing_live (program : Λ → TM2.Stmt Γ Λ σ) (cfg : TM2.Cfg Γ Λ σ)
    (label : Λ) (live : cfg.l = some label) :
    absorbingNext (TM2.step program) cfg = TM2.stepAux (program label) cfg.var cfg.stk := by
  cases cfg with
  | mk l v tapes =>
    change l = some label at live
    subst l
    rfl

omit [Fintype Λ] [DecidableEq Λ] [Fintype σ] [DecidableEq σ]
  [∀ stack, Fintype (Γ stack)] [∀ stack, DecidableEq (Γ stack)] in
theorem absorbing_halted (program : Λ → TM2.Stmt Γ Λ σ) (cfg : TM2.Cfg Γ Λ σ)
    (halted : cfg.l = none) : absorbingNext (TM2.step program) cfg = cfg := by
  apply absorbingNext_of_none
  cases cfg with
  | mk l v tapes =>
    change l = none at halted
    subst l
    rfl

omit [Fintype Λ] in
theorem liveCase_eval (S : Nat) (program : Λ → TM2.Stmt Γ Λ σ)
    (cfg : TM2.Cfg Γ Λ σ) (safe : StepSafe S program cfg)
    (bit : ConfigBit Γ Λ σ S) (label : Λ) :
    (liveCase S program bit label).eval (configEncoding S cfg) =
      (decide (cfg.l = some label) &&
        configEncoding S (absorbingNext (TM2.step program) cfg) bit) := by
  by_cases live : cfg.l = some label
  · simp only [liveCase, Expr.eval, Expr.eval_rename, configEncoding, live,
      decide_true, Bool.true_and]
    rw [transitionExpr_eval S (program label) cfg.var cfg.stk (safe label live),
      absorbing_live program cfg label live]
    rfl
  · simp [liveCase, Expr.eval, configEncoding, live]

theorem stickyExpr_eval (S : Nat) (program : Λ → TM2.Stmt Γ Λ σ)
    (cfg : TM2.Cfg Γ Λ σ) (safe : StepSafe S program cfg)
    (bit : ConfigBit Γ Λ σ S) :
    (stickyExpr S program bit).eval (configEncoding S cfg) =
      configEncoding S (absorbingNext (TM2.step program) cfg) bit := by
  have hactive :
      (Expr.disjoin (Finset.univ.toList.map (liveCase S program bit))).eval
        (configEncoding S cfg) = true ↔
      ∃ label, cfg.l = some label ∧
        configEncoding S (absorbingNext (TM2.step program) cfg) bit = true := by
    rw [Expr.eval_disjoin_true]
    simp only [List.mem_map]
    constructor
    · rintro ⟨e, ⟨label, _, rfl⟩, he⟩
      rw [liveCase_eval S program cfg safe] at he
      exact ⟨label, by simpa only [Bool.and_eq_true, decide_eq_true_eq] using he⟩
    · rintro ⟨label, hl, hb⟩
      refine ⟨liveCase S program bit label, ?_, ?_⟩
      · exact ⟨label, by simp, rfl⟩
      · rw [liveCase_eval S program cfg safe]
        simp [hl, hb]
  apply bool_ext
  simp only [stickyExpr, Expr.eval, Bool.or_eq_true, Bool.and_eq_true, hactive]
  cases hl : cfg.l with
  | none =>
    rw [absorbing_halted program cfg hl]
    simp [configEncoding, hl]
  | some label => simp [configEncoding, hl]

omit [DecidableEq K] [Fintype Λ] [Fintype σ] [∀ stack, Fintype (Γ stack)] in
theorem configEncoding_injective (S : Nat) (first second : TM2.Cfg Γ Λ σ)
    (hfirst : ∀ k, (first.stk k).length ≤ S)
    (hsecond : ∀ k, (second.stk k).length ≤ S)
    (same : configEncoding S first = configEncoding S second) : first = second := by
  have hl : first.l = second.l := by
    have h := congrFun same (.inl second.l)
    simpa only [configEncoding, decide_true, decide_eq_true_eq] using h
  have hv : first.var = second.var := by
    have h := congrFun same (.inr (.inl second.var))
    simpa only [configEncoding, inputEncoding, decide_true, decide_eq_true_eq] using h
  have ht : first.stk = second.stk := by
    funext k
    apply StackEncoding.encode_injective (hfirst k) (hsecond k)
    funext i
    have h := congrFun same (.inr (.inr ⟨k, i, StackEncoding.encode S (second.stk k) i⟩))
    simpa only [configEncoding, inputEncoding, decide_true, decide_eq_true_eq] using h
  cases first
  cases second
  simp only at hl hv ht
  cases hl
  cases hv
  cases ht
  rfl

noncomputable def programCost (program : Λ → TM2.Stmt Γ Λ σ) : Nat :=
  ∑ label, statementCost (program label) 1

omit [DecidableEq K] [DecidableEq Λ] [DecidableEq σ]
  [∀ stack, DecidableEq (Γ stack)] in
theorem statementCost_le_programCost (program : Λ → TM2.Stmt Γ Λ σ) (label : Λ) :
    statementCost (program label) 1 ≤ programCost program := by
  unfold programCost
  exact Finset.single_le_sum (f := fun i : Λ => statementCost (program i) 1)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ label)

noncomputable def expressionCost (program : Λ → TM2.Stmt Γ Λ σ) : Nat :=
  5 + Fintype.card Λ * (programCost program + 3)

omit [DecidableEq K] [DecidableEq Λ] [DecidableEq σ]
  [∀ stack, DecidableEq (Γ stack)] in
theorem one_le_expressionCost (program : Λ → TM2.Stmt Γ Λ σ) :
    1 ≤ expressionCost program := by
  unfold expressionCost
  omega

theorem stickyExpr_size_le (S : Nat) (program : Λ → TM2.Stmt Γ Λ σ)
    (bit : ConfigBit Γ Λ σ S) :
    (stickyExpr S program bit).size ≤ expressionCost program := by
  have hc : ∀ e ∈ Finset.univ.toList.map (liveCase S program bit),
      e.size ≤ programCost program + 2 := by
    intro e he
    rcases List.mem_map.mp he with ⟨label, _, rfl⟩
    have h := (transitionExpr_size_le S (program label) bit).trans
      (statementCost_le_programCost program label)
    simp only [liveCase, Expr.size, Expr.size_rename]
    omega
  have hd := Expr.size_disjoin_le
    (Finset.univ.toList.map (liveCase S program bit)) (programCost program + 2) hc
  simp only [List.length_map, Finset.length_toList, Finset.card_univ] at hd
  simp only [Nat.add_assoc] at hd
  rw [show (2 : Nat) + 1 = 3 by decide] at hd
  simp only [stickyExpr, Expr.size, expressionCost]
  omega

end BinPackingGames.Foundations.Complexity.CookLevin.MachineCircuit

end OAI
