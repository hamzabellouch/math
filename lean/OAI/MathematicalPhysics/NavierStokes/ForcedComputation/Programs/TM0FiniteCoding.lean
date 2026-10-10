import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.TM0TableSimulation

namespace OAI

/-! Finite support is sufficient for a fixed TM0 program to have a genuine
finite table.  Only the input word varies in this conversion. -/

namespace ForcedComputation.FiniteMachine

open Turing

theorem exists_pointed_fin_equiv (A : Type*) [Fintype A] [Inhabited A] :
    ∃ n : ℕ, ∃ e : A ≃ Fin (n + 1), e default = 0 := by
  classical
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero
    (ne_of_gt (Fintype.card_pos : 0 < Fintype.card A))
  let e : A ≃ Fin (n + 1) := Fintype.equivFinOfCardEq hn
  exact ⟨n, e.trans (Equiv.swap (e default) 0), by simp⟩

theorem map_eval_dom {Γ Λ Γ' Λ' : Type*}
    [Inhabited Γ] [Inhabited Λ] [Inhabited Γ'] [Inhabited Λ']
    (M : TM0.Machine Γ Λ) (S : Set Λ) (hS : TM0.Supports M S)
    (f : PointedMap Γ Γ') (f' : PointedMap Γ' Γ)
    (q : PointedMap Λ Λ') (q' : Λ' → Λ)
    (hf : Function.RightInverse f f')
    (hq : ∀ a ∈ S, q' (q a) = a) (w : List Γ) :
    (TM0.eval (M.map f f' q q') (w.map f)).Dom ↔ (TM0.eval M w).Dom := by
  have hr := M.map_respects f f' q q' hS hf hq
  have hi : (TM0.init w : TM0.Cfg Γ Λ).q ∈ S ∧
      TM0.Cfg.map f q (TM0.init w) = TM0.init (w.map f) :=
    ⟨hS.1, TM0.map_init f q w⟩
  exact StateTransition.tr_eval_dom hr hi

theorem finite_supported_TM0 {Γ Λ : Type*} [Fintype Γ] [Inhabited Γ]
    [Inhabited Λ] [DecidableEq Λ]
    (M : TM0.Machine Γ Λ) (S : Finset Λ) (hS : TM0.Supports M (S : Set Λ)) :
    ∃ g q : ℕ, ∃ N : TM0.Machine (Fin (g + 1)) (Fin (q + 1)),
      ∃ e : Γ ≃ Fin (g + 1), e default = 0 ∧
        ∀ w, (TM0.eval N (w.map e)).Dom ↔ (TM0.eval M w).Dom := by
  classical
  let : Inhabited S := ⟨⟨default, hS.1⟩⟩
  obtain ⟨g, e, he⟩ := exists_pointed_fin_equiv Γ
  obtain ⟨q, d, hd⟩ := exists_pointed_fin_equiv S
  let f : PointedMap Γ (Fin (g + 1)) := ⟨e, he⟩
  let f' : PointedMap (Fin (g + 1)) Γ := ⟨e.symm, by
    apply e.injective
    simpa only [Equiv.apply_symm_apply, Fin.default_eq_zero] using he.symm⟩
  let d₁ : PointedMap Λ (Fin (q + 1)) :=
    ⟨fun a => if h : a ∈ S then d ⟨a, h⟩ else 0, by
      have hs : (default : Λ) ∈ S := hS.1
      rw [dite_eq_left hs, Fin.default_eq_zero]
      exact hd⟩
  let d₂ : Fin (q + 1) → Λ := fun a => (d.symm a).val
  refine ⟨g, q, M.map f f' d₁ d₂, e, he, ?_⟩
  intro w
  apply map_eval_dom M (S : Set Λ) hS f f' d₁ d₂
  · intro a
    exact e.symm_apply_apply a
  · intro a ha
    have ha' : a ∈ S := ha
    change (d.symm (if h : a ∈ S then d ⟨a, h⟩ else 0)).val = a
    rw [dite_eq_left ha']
    exact congrArg Subtype.val (d.symm_apply_apply ⟨a, ha⟩)

end ForcedComputation.FiniteMachine

end OAI
