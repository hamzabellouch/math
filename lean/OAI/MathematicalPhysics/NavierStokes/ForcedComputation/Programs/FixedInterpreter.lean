import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.TM0FiniteCoding
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.TuringInputEncoding
import Mathlib.Computability.Halting

namespace OAI

/-! One fixed finite interpreter and a computable input encoding.  Arbitrary
partial-recursive programs enter as input data, not as varying machine tables. -/

namespace ForcedComputation.FiniteMachine

open Turing Alternating

theorem exists_universal_list_code :
    ∃ c : ToPartrec.Code, ∀ n : ℕ,
      (c.eval [n]).Dom ↔ ((Denumerable.ofNat Nat.Partrec.Code n).eval 0).Dom := by
  have hf : Partrec (fun n : ℕ => (Denumerable.ofNat Nat.Partrec.Code n).eval 0) :=
    Nat.Partrec.Code.eval_part.comp (Computable.ofNat _) (Computable.const 0)
  obtain ⟨c, hc⟩ := ToPartrec.Code.exists_code (Nat.Partrec'.part_iff₁.mpr hf)
  refine ⟨c, fun n => ?_⟩
  have h := congrArg Part.Dom (hc ⟨[n], rfl⟩)
  exact iff_of_eq h

theorem fixed_list_TM0 (c : ToPartrec.Code) :
    ∃ g q : ℕ, ∃ M : TM0.Machine (Fin (g + 1)) (Fin (q + 1)),
      ∃ input : List ℕ → List (Fin (g + 1)),
        Computable input ∧ ∀ v, (TM0.eval M (input v)).Dom ↔ (c.eval v).Dom := by
  classical
  let : Inhabited PartrecToTM2.Λ' :=
    ⟨PartrecToTM2.trNormal c PartrecToTM2.Cont'.halt⟩
  let : Fintype PartrecToTM2.K' :=
    ⟨{.main, .rev, .aux, .stack}, by intro k; cases k <;> simp⟩
  let Γ : Type := TM2to1.Γ' PartrecToTM2.K' (fun _ => PartrecToTM2.Γ')
  let m₁ := TM2to1.tr PartrecToTM2.tr
  let m₀ := TM1to0.tr m₁
  let S₁ := TM2to1.trSupp PartrecToTM2.tr
    (PartrecToTM2.codeSupp c PartrecToTM2.Cont'.halt)
  have hs₁ : TM1.Supports m₁ S₁ :=
    TM2to1.tr_supports _ (PartrecToTM2.tr_supports c PartrecToTM2.Cont'.halt)
  have hs₀ := TM1to0.tr_supports m₁ hs₁
  obtain ⟨g, q, N, e, he, hN⟩ := finite_supported_TM0 m₀
    (TM1to0.trStmts m₁ S₁) hs₀
  let : Primcodable PartrecToTM2.Γ' :=
    Primcodable.ofEquiv (Fin (Fintype.card PartrecToTM2.Γ'))
      (Fintype.equivFin PartrecToTM2.Γ')
  let : Primcodable Γ := Primcodable.ofEquiv (Fin (g + 1)) e
  let input : List ℕ → List (Fin (g + 1)) := fun v =>
    (TM2to1.trInit PartrecToTM2.K'.main (PartrecToTM2.trList v)).map e
  have hin : Computable input := by
    apply Primrec.to_comp
    exact Primrec.list_map
      ((trInit_primrec PartrecToTM2.K'.main).comp trList_primrec)
      ((Primrec.dom_finite (fun a : Γ => e a)).comp Primrec.snd).to₂
  refine ⟨g, q, N, input, hin, fun v => ?_⟩
  change (TM0.eval N ((TM2to1.trInit PartrecToTM2.K'.main
    (PartrecToTM2.trList v)).map e)).Dom ↔ _
  apply (hN _).trans
  rw [TM1to0.tr_eval]
  apply (TM2to1.tr_eval_dom (M := PartrecToTM2.tr)
    PartrecToTM2.K'.main (PartrecToTM2.trList v)).trans
  have hi : (TM2.init PartrecToTM2.K'.main (PartrecToTM2.trList v) :
      TM2.Cfg (fun _ : PartrecToTM2.K' => PartrecToTM2.Γ')
        PartrecToTM2.Λ' (Option PartrecToTM2.Γ')) = PartrecToTM2.init c v := by
    unfold TM2.init PartrecToTM2.init
    congr 1
    funext k
    cases k <;> rfl
  change (StateTransition.eval (TM2.step PartrecToTM2.tr)
    (TM2.init PartrecToTM2.K'.main (PartrecToTM2.trList v))).Dom ↔ _
  rw [hi, PartrecToTM2.tr_eval]
  rfl

theorem exists_fixed_universal_TM0 :
    ∃ g q : ℕ, ∃ M : TM0.Machine (Fin (g + 1)) (Fin (q + 1)),
      ∃ input : ℕ → List (Fin (g + 1)),
        Computable input ∧ ∀ n, (TM0.eval M (input n)).Dom ↔
          ((Denumerable.ofNat Nat.Partrec.Code n).eval 0).Dom := by
  obtain ⟨c, hc⟩ := exists_universal_list_code
  obtain ⟨g, q, M, input, hi, hM⟩ := fixed_list_TM0 c
  refine ⟨g, q, M, fun n => input [n], hi.comp ?_, fun n => (hM [n]).trans (hc n)⟩
  exact Computable.list_cons.comp Computable.id (Computable.const [])

theorem exists_fixed_universal_machine :
    ∃ M : Machine, ∃ input : ℕ → List ℕ,
      Computable input ∧ ∀ n,
        ValidInput (M, input n) ∧
          (Halts (M, input n) ↔ ((Denumerable.ofNat Nat.Partrec.Code n).eval 0).Dom) := by
  obtain ⟨g, q, M, input, hi, hM⟩ := exists_fixed_universal_TM0
  have hv : Computable (fun w : List (Fin (g + 1)) => w.map Fin.val) :=
    (Primrec.list_map Primrec.id
      ((Primrec.dom_finite Fin.val).comp Primrec.snd).to₂).to_comp
  refine ⟨compileTM0 M, fun n => (input n).map Fin.val,
    hv.comp hi, fun n => ⟨compileTM0Input_valid M (input n), ?_⟩⟩
  exact (compileTM0_halts_iff M (input n)).trans (hM n)

end ForcedComputation.FiniteMachine

end OAI
