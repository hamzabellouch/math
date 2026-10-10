import OAI.Computability.BinPacking.Packing.PairExpressionCompiler

namespace OAI

noncomputable section

namespace BinPackingGap.ResetExpressionCompiler

open NatExpressionCompiler BinaryRegisterProgram PairExpressionCompiler

variable {α Reg : Type} [DecidableEq Reg]

def nodeList (expression : Expr α) (nodes : Node expression ↪ Reg) : List Reg :=
  (Finset.univ : Finset (Node expression)).toList.map nodes

omit [DecidableEq Reg] in
theorem mem_nodeList (expression : Expr α) (nodes : Node expression ↪ Reg) (r : Reg) :
    r ∈ nodeList expression nodes ↔ ∃ n, r = nodes n := by
  simp [nodeList, eq_comm]

def commands (inputs : α → Reg) (expression : Expr α)
    (nodes : Node expression ↪ Reg) (apart : ∀ a n, inputs a ≠ nodes n)
    (output : Reg) (outputApart : ∀ n, output ≠ nodes n) : List (Command Reg) :=
  .clear output :: (compileInto inputs expression nodes apart ++
    (.copy output (nodes (root expression)) (outputApart _) ::
      clearList (nodeList expression nodes)))

theorem correct (inputs : α → Reg) (expression : Expr α)
    (nodes : Node expression ↪ Reg) (apart : ∀ a n, inputs a ≠ nodes n)
    (output : Reg) (outputApart : ∀ n, output ≠ nodes n)
    (inputOutput : ∀ a, inputs a ≠ output)
    (values : Reg → Nat) (empty : ∀ n, values (nodes n) = 0) :
    Ready (commands inputs expression nodes apart output outputApart) values ∧
      resultOf (commands inputs expression nodes apart output outputApart) values =
        Function.update values output (eval (fun a => values (inputs a)) expression) := by
  let reset := result (.clear output) values
  let calculated := resultOf (compileInto inputs expression nodes apart) reset
  have resetNodes : ∀ n, reset (nodes n) = 0 := by
    intro n
    simp [reset, result, destination, value, Ne.symm (outputApart n), empty n]
  have resetInputs : ∀ a, reset (inputs a) = values (inputs a) := by
    intro a
    simp [reset, result, destination, value, inputOutput a]
  have compiled := compileInto_correct inputs expression nodes apart reset resetNodes
  have outputZero : calculated output = 0 := by
    rw [show calculated output = reset output from compiled.2.2 output outputApart]
    simp [reset, result, destination, value]
  have rootValue : calculated (nodes (root expression)) =
      eval (fun a => values (inputs a)) expression := by
    simpa only [calculated, resetInputs] using compiled.2.1
  constructor
  · change True ∧ Ready (compileInto inputs expression nodes apart ++ _) reset
    refine ⟨True.intro, ?_⟩
    rw [Ready_append]
    refine ⟨compiled.1, ?_⟩
    change calculated output = 0 ∧ _
    exact ⟨outputZero, clearList_ready _ _⟩
  · funext r
    simp only [commands, resultOf_cons, resultOf_append]
    rw [clearList_result]
    by_cases member : r ∈ nodeList expression nodes
    · obtain ⟨n, rfl⟩ := (mem_nodeList expression nodes r).mp member
      simp only [ite_eq_left member]
      simp [Ne.symm (outputApart n), empty n]
    · rw [ite_eq_right member]
      have outside : ∀ n, r ≠ nodes n := by
        intro n hn
        exact member ((mem_nodeList expression nodes r).mpr ⟨n, hn⟩)
      by_cases same : r = output
      · subst r
        simpa only [calculated, reset, result, destination, value, Function.update_self] using rootValue
      · have preserved : calculated r = reset r := compiled.2.2 r outside
        change (result (.copy output (nodes (root expression)) (outputApart _))
          calculated) r = Function.update values output _ r
        rw [result_other _ _ _ same, preserved]
        simp [reset, result, destination, value, same]

end BinPackingGap.ResetExpressionCompiler

end

end OAI
