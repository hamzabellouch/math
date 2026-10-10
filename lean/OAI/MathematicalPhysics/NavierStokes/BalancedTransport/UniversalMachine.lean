import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.UniversalInput

namespace OAI

noncomputable section
namespace BalancedTransport.Universal
open Turing PartrecToTM2 StateTransition
open scoped Classical

theorem finite_machine_of_code (c : ToPartrec.Code) :
    ∃ M : FiniteMachine, ∃ δ : ℕ → Input M,
      Computable δ ∧ ∀ n, Halts M (δ n) ↔ (c.eval [n]).Dom := by
  let : Inhabited PartrecToTM2.Λ' := ⟨trNormal c Cont'.halt⟩
  let P₁ := TM2to1.tr PartrecToTM2.tr
  let S₁ := TM2to1.trSupp PartrecToTM2.tr (codeSupp c Cont'.halt)
  have ss₁ : TM1.Supports P₁ S₁ := TM2to1.tr_supports PartrecToTM2.tr (PartrecToTM2.tr_supports c Cont'.halt)
  let P₀ := TM1to0.tr P₁
  let S₀ := TM1to0.trStmts P₁ S₁
  have ss₀ : TM0.Supports P₀ S₀ := TM1to0.tr_supports P₁ ss₁
  let δ : ℕ → List (Fin (Fintype.card StackAlphabet + 1)) := fun n =>
    (TM2to1.trInit (Γ := fun _ : K' => Γ') K'.main (trList [n])).map
      (finiteIndex (α := StackAlphabet))
  refine ⟨finitePostMachine P₀ S₀ ss₀, δ, computable_translatedInput, ?_⟩
  intro n
  rw [halts_finitePostMachine, TM1to0.tr_eval]
  refine (TM2to1.tr_eval_dom PartrecToTM2.tr K'.main (trList [n])).trans ?_
  have hi : (TM2.init K'.main (trList [n]) : TM2.Cfg (fun _ : K' => Γ') PartrecToTM2.Λ' (Option Γ')) =
      PartrecToTM2.init c [n] := by
    unfold TM2.init PartrecToTM2.init
    congr 1
    funext k
    cases k <;> simp [K'.elim,Function.update]
  change (eval (TM2.step PartrecToTM2.tr) (TM2.init K'.main (trList [n]))).Dom ↔ _
  rw [hi, PartrecToTM2.tr_eval]
  rfl

theorem exists_universal_machine :
    ∃ N : FiniteMachine, ∃ δ : ℕ → Input N,
      Computable δ ∧ ∀ M w, Halts N (δ (inputCode M w)) ↔ Halts M w := by
  obtain ⟨c,hc⟩ := exists_universal_code
  obtain ⟨N,δ,hδ,hh⟩ := finite_machine_of_code c
  exact ⟨N,δ,hδ, fun M w => (hh _).trans ((hc _).trans (universalPartial_dom M w))⟩

end BalancedTransport.Universal
end

end OAI
