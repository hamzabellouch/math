import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.TM0TableSimulation
import OAI.MathematicalPhysics.RapidForcing.Model

namespace OAI

/-! The same finite TM0 table in the bounded-state presentation used by the
rapid-forcing development. -/

namespace ForcedComputation.FiniteMachine

open Turing Alternating

def rapidAction {g q : ℕ} (a : Fin (g + 1)) :
    Fin (q + 1) × TM0.Stmt (Fin (g + 1)) →
      Fin (q + 1) × Fin (g + 1) × Fin 3
  | (r, .move .left) => (r, a, 0)
  | (r, .move .right) => (r, a, 2)
  | (r, .write b) => (r, b, 1)

def rapidTM0 {g q : ℕ} (M : TM0.Machine (Fin (g + 1)) (Fin (q + 1))) :
    RapidForcing.Machine where
  states := q + 1
  symbols := g + 1
  states_pos := Nat.succ_pos _
  symbols_pos := Nat.succ_pos _
  initial := 0
  transition r a := (M r a).map (rapidAction a)

def eraseRapid {g q : ℕ} {M : TM0.Machine (Fin (g + 1)) (Fin (q + 1))}
    (c : (rapidTM0 M).Config) : Configuration :=
  ⟨c.state.val, c.head, fun j => (c.tape j).val⟩

theorem val_update {g : ℕ} (t : ℤ → Fin (g + 1)) (h : ℤ)
    (a : Fin (g + 1)) :
    (fun j => (Function.update t h a j).val) =
      Function.update (fun j => (t j).val) h a.val := by
  funext j
  exact Function.apply_update (fun _ (a : Fin (g + 1)) => a.val) t h a j

theorem eraseRapid_step {g q : ℕ}
    (M : TM0.Machine (Fin (g + 1)) (Fin (q + 1)))
    (c : (rapidTM0 M).Config) :
    eraseRapid ((rapidTM0 M).nextConfig c) = (compileTM0 M).step (eraseRapid c) := by
  by_cases hr : c.state.val < q + 1
  · have hh := compileTM0_not_halting M ⟨c.state.val, hr⟩
    have hi := compileTM0_instruction M ⟨c.state.val, hr⟩ (c.tape c.head)
    cases hm : M ⟨c.state.val, hr⟩ (c.tape c.head) with
    | none =>
      simp only [RapidForcing.Machine.nextConfig, rapidTM0, hr, ↓reduceDIte,
        hm, Option.map_none, eraseRapid, Machine.step, hh, Bool.false_eq_true,
        ↓reduceIte, hi, compileTM0_stateCount]
    | some rs =>
      rcases rs with ⟨r, s⟩
      cases s with
      | move d =>
        cases d <;>
          simp [RapidForcing.Machine.nextConfig, rapidTM0, hr, hm, eraseRapid,
            Machine.step, hh, hi, rapidAction, encodeAction]
      | write a =>
        simp [RapidForcing.Machine.nextConfig, rapidTM0, hr, hm, eraseRapid,
          Machine.step, hh, hi, rapidAction, encodeAction, val_update]
  · have hs : c.state.val = q + 1 := by
      have hb : c.state.val < q + 2 := c.state.isLt
      omega
    have hh : (compileTM0 M).isHalting (eraseRapid c).state = true := by
      change decide (c.state.val = q + 1 ∨ c.state.val ∈ (∅ : Finset ℕ)) = true
      simp only [hs, true_or, decide_true]
    simp only [RapidForcing.Machine.nextConfig, rapidTM0, hr, ↓reduceDIte,
      Machine.step, hh, ↓reduceIte]

theorem eraseRapid_initial {g q : ℕ}
    (M : TM0.Machine (Fin (g + 1)) (Fin (q + 1))) (w : List (Fin (g + 1))) :
    eraseRapid ((rapidTM0 M).initialConfig w) = initialConfiguration (w.map Fin.val) := by
  apply configuration_ext
  · rfl
  · rfl
  · funext j
    by_cases hj : 0 ≤ j
    · change (if 0 ≤ j then (w[j.toNat]?).getD (0 : Fin (g + 1)) else 0).val =
        if j < 0 then 0 else ((w.map Fin.val)[j.toNat]?).getD 0
      simp only [hj, not_lt_of_ge hj, ↓reduceIte, List.getElem?_map]
      exact (Option.getD_map Fin.val (0 : Fin (g + 1)) _).symm
    · simp [eraseRapid, RapidForcing.Machine.initialConfig,
        initialConfiguration, hj, lt_of_not_ge hj, RapidForcing.Machine.blank, rapidTM0]

theorem eraseRapid_run {g q : ℕ}
    (M : TM0.Machine (Fin (g + 1)) (Fin (q + 1))) (w : List (Fin (g + 1))) (n : ℕ) :
    eraseRapid ((rapidTM0 M).run w n) =
      (compileTM0 M).step^[n] (initialConfiguration (w.map Fin.val)) := by
  induction n with
  | zero => exact eraseRapid_initial M w
  | succ n ih =>
    have he := (eraseRapid_step M _).trans (congrArg (compileTM0 M).step ih)
    simpa only [RapidForcing.Machine.run, Function.iterate_succ_apply'] using he

theorem rapidTM0_halts_iff {g q : ℕ}
    (M : TM0.Machine (Fin (g + 1)) (Fin (q + 1))) (w : List (Fin (g + 1))) :
    (rapidTM0 M).Halts w ↔ (TM0.eval M w).Dom := by
  rw [← compileTM0_halts_iff]
  change (∃ n, ((rapidTM0 M).run w n).state.val = q + 1) ↔
    ∃ n, (compileTM0 M).isHalting
      ((compileTM0 M).step^[n] (initialConfiguration (w.map Fin.val))).state = true
  apply exists_congr
  intro n
  rw [← eraseRapid_run M w n]
  change _ ↔ decide (((rapidTM0 M).run w n).state.val = q + 1 ∨
    ((rapidTM0 M).run w n).state.val ∈ (∅ : Finset ℕ)) = true
  simp only [Finset.notMem_empty, or_false, decide_eq_true_eq]

end ForcedComputation.FiniteMachine

end OAI
