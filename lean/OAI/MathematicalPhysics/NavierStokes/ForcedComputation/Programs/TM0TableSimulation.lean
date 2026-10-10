import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.TM0FiniteTable

namespace OAI

/-! Exact tape simulation of a finite TM0 machine by the fluid source model. -/

namespace ForcedComputation.FiniteMachine

open Alternating Turing

theorem configuration_ext {c d : Configuration} (hs : c.state = d.state)
    (hh : c.head = d.head) (ht : c.tape = d.tape) : c = d := by
  cases c
  cases d
  cases hs
  cases hh
  cases ht
  rfl

def embedConfiguration {g q : ℕ}
    (c : TM0.Cfg (Fin (g + 1)) (Fin (q + 1))) (h : ℤ) : Configuration :=
  { state := c.q.val
    head := h
    tape := fun j => (c.Tape.nth (j - h)).val }

def actionDisplacement {g : ℕ} : TM0.Stmt (Fin (g + 1)) → ℤ
  | .move .left => -1
  | .move .right => 1
  | .write _ => 0

def actionTape {g : ℕ} (s : TM0.Stmt (Fin (g + 1)))
    (T : Tape (Fin (g + 1))) : Tape (Fin (g + 1)) :=
  match s with
  | .move d => T.move d
  | .write a => T.write a

theorem embedConfiguration_action {g q : ℕ}
    (c : TM0.Cfg (Fin (g + 1)) (Fin (q + 1))) (h : ℤ)
    (r : Fin (q + 1)) (s : TM0.Stmt (Fin (g + 1))) :
    ({ state := (encodeAction c.Tape.head (r, s)).1
       head := h + ((encodeAction c.Tape.head (r, s)).2.2.val : ℤ) - 1
       tape := Function.update (embedConfiguration c h).tape h
         (encodeAction c.Tape.head (r, s)).2.1 } : Configuration) =
      embedConfiguration ⟨r, actionTape s c.Tape⟩ (h + actionDisplacement s) := by
  cases s with
  | move d =>
    cases d with
    | left =>
      apply configuration_ext
      · rfl
      · dsimp [embedConfiguration, actionDisplacement, encodeAction]
        omega
      · funext j
        have hi : j - (h + -1) - 1 = j - h := by omega
        by_cases hj : j = h
        · subst j
          simp [embedConfiguration, actionTape, actionDisplacement, encodeAction]
        · simp [embedConfiguration, actionTape, actionDisplacement, encodeAction,
            Function.update_of_ne hj, hi]
    | right =>
      apply configuration_ext
      · rfl
      · dsimp [embedConfiguration, actionDisplacement, encodeAction]
        omega
      · funext j
        have hi : j - (h + 1) + 1 = j - h := by omega
        by_cases hj : j = h
        · subst j
          simp [embedConfiguration, actionTape, actionDisplacement, encodeAction]
        · simp [embedConfiguration, actionTape, actionDisplacement, encodeAction,
            Function.update_of_ne hj, hi]
  | write a =>
    apply configuration_ext
    · rfl
    · simp [embedConfiguration, actionDisplacement, encodeAction]
    · funext j
      by_cases hj : j = h
      · subst j
        simp [embedConfiguration, actionTape, actionDisplacement, encodeAction]
      · have hd : j - h ≠ 0 := sub_ne_zero.mpr hj
        simp [embedConfiguration, actionTape, actionDisplacement, encodeAction,
          Function.update_of_ne hj, hd]

theorem partialStep_embed {g q : ℕ}
    (M : TM0.Machine (Fin (g + 1)) (Fin (q + 1)))
    (c : TM0.Cfg (Fin (g + 1)) (Fin (q + 1))) (h : ℤ) :
    partialStep (compileTM0 M) (embedConfiguration c h) =
      (M c.q c.Tape.head).map (fun rs =>
        embedConfiguration ⟨rs.1, actionTape rs.2 c.Tape⟩
          (h + actionDisplacement rs.2)) := by
  unfold partialStep
  simp only [embedConfiguration, compileTM0_not_halting, Bool.false_eq_true,
    ↓reduceIte, sub_self, Tape.nth_zero, compileTM0_instruction]
  cases hm : M c.q c.Tape.head with
  | none => rfl
  | some rs =>
    simp only [Option.map_some]
    exact congrArg some (embedConfiguration_action c h rs.1 rs.2)

def ConfigurationRelation {g q : ℕ}
    (c : TM0.Cfg (Fin (g + 1)) (Fin (q + 1))) (d : Configuration) : Prop :=
  ∃ h, embedConfiguration c h = d

theorem compileTM0_respects {g q : ℕ}
    (M : TM0.Machine (Fin (g + 1)) (Fin (q + 1))) :
    StateTransition.Respects (TM0.step M) (partialStep (compileTM0 M))
      ConfigurationRelation := by
  rintro c _ ⟨h, rfl⟩
  cases hm : M c.q c.Tape.head with
  | none =>
    simp only [TM0.step, hm, Option.map_none]
    simp only [partialStep_embed, hm, Option.map_none]
  | some rs =>
    simp only [TM0.step, hm, Option.map_some]
    refine ⟨embedConfiguration ⟨rs.1, actionTape rs.2 c.Tape⟩
      (h + actionDisplacement rs.2), ?_, .single ?_⟩
    · refine ⟨h + actionDisplacement rs.2, ?_⟩
      cases rs.2 <;> rfl
    exact (partialStep_embed M c h).trans (by rw [hm]; rfl)

theorem embedConfiguration_initial {g q : ℕ} (w : List (Fin (g + 1))) :
    embedConfiguration (TM0.init w : TM0.Cfg (Fin (g + 1)) (Fin (q + 1))) 0 =
      initialConfiguration (w.map Fin.val) := by
  apply configuration_ext
  · rfl
  · rfl
  · funext j
    cases j with
    | ofNat n =>
      change ((Tape.mk₁ w).nth (n : ℤ)).val =
        if (n : ℤ) < 0 then 0 else ((w.map Fin.val)[n]?).getD 0
      simp only [show ¬ (n : ℤ) < 0 from not_lt_of_ge (Int.natCast_nonneg n),
        ↓reduceIte, Tape.mk₁, Tape.mk₂, Tape.mk'_nth_nat, ListBlank.nth_mk,
        List.getElem?_map, List.getI_eq_getElem?_getD]
      cases w[n]? <;> rfl
    | negSucc n =>
      simp [embedConfiguration, TM0.init, initialConfiguration, Tape.mk₁,
        Tape.mk₂, Tape.mk', Tape.nth]

theorem compileTM0_halts_iff {g q : ℕ}
    (M : TM0.Machine (Fin (g + 1)) (Fin (q + 1)))
    (w : List (Fin (g + 1))) :
    Halts (compileTM0Input M w) ↔ (TM0.eval M w).Dom := by
  rw [halts_iff_eval_dom]
  change (StateTransition.eval (partialStep (compileTM0 M))
    (initialConfiguration (w.map Fin.val))).Dom ↔ _
  rw [← embedConfiguration_initial]
  have h := StateTransition.tr_eval_dom (compileTM0_respects M)
    (show ConfigurationRelation (TM0.init w) (embedConfiguration (TM0.init w) 0)
      from ⟨0, rfl⟩)
  exact h

end ForcedComputation.FiniteMachine

end OAI
