import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.TM0RapidPresentation
import OAI.MathematicalPhysics.AlternatingFlow.Model

namespace OAI

/-! Flattening the fixed finite interpreter into the alternating-flow input
format changes only the storage layout of its transition table. -/

namespace ForcedComputation.FiniteMachine

open Turing

def alternatingTM0 {g q : ℕ}
    (M : TM0.Machine (Fin (g + 1)) (Fin (q + 1))) : AlternatingNS.Machine :=
  (q, g, 0, [], List.ofFn fun i : Fin ((q + 1) * (g + 1)) =>
    let a : Fin (g + 1) := ⟨i.val % (g + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
    let r : Fin (q + 1) := ⟨i.val / (g + 1),
      (Nat.div_lt_iff_lt_mul (Nat.succ_pos g)).mpr i.isLt⟩
    (M r a).map (encodeAction a))

theorem alternatingTM0_instruction {g q : ℕ}
    (M : TM0.Machine (Fin (g + 1)) (Fin (q + 1)))
    (r : Fin (q + 1)) (a : Fin (g + 1)) :
    (alternatingTM0 M).instruction r.val a.val = (M r a).map (encodeAction a) := by
  have hi : r.val * (g + 1) + a.val < (q + 1) * (g + 1) := by
    calc
      _ < r.val * (g + 1) + (g + 1) := Nat.add_lt_add_left a.isLt _
      _ = (r.val + 1) * (g + 1) := by rw [Nat.add_mul, one_mul]
      _ ≤ (q + 1) * (g + 1) := Nat.mul_le_mul_right _ r.isLt
  have hd : (r.val * (g + 1) + a.val) / (g + 1) = r.val := by
    rw [Nat.mul_comm r.val, Nat.mul_add_div (Nat.succ_pos _),
      Nat.div_eq_of_lt a.isLt, Nat.add_zero]
  have hm : (r.val * (g + 1) + a.val) % (g + 1) = a.val :=
    Nat.mul_add_mod_of_lt a.isLt
  change ((List.ofFn fun i : Fin ((q + 1) * (g + 1)) =>
    let a : Fin (g + 1) := ⟨i.val % (g + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
    let r : Fin (q + 1) := ⟨i.val / (g + 1),
      (Nat.div_lt_iff_lt_mul (Nat.succ_pos g)).mpr i.isLt⟩
    (M r a).map (encodeAction a))[r.val * (g + 1) + a.val]?).join = _
  simp only [List.getElem?_ofFn, hi, ↓reduceDIte, Option.join_some, hd, hm]

theorem alternatingTM0_wellFormed {g q : ℕ}
    (M : TM0.Machine (Fin (g + 1)) (Fin (q + 1))) :
    (alternatingTM0 M).WellFormed := by
  refine ⟨Nat.succ_pos _, by simp [alternatingTM0, AlternatingNS.Machine.haltingStates], ?_⟩
  intro r a s hr ha hs
  change r < q + 1 at hr
  change a < g + 1 at ha
  rw [alternatingTM0_instruction M ⟨r, hr⟩ ⟨a, ha⟩] at hs
  obtain ⟨v, _, rfl⟩ := Option.map_eq_some_iff.mp hs
  exact encodeAction_bounds ⟨a, ha⟩ v

def eraseAlternating {g q : ℕ} {M : TM0.Machine (Fin (g + 1)) (Fin (q + 1))}
    (c : (rapidTM0 M).Config) : AlternatingNS.Machine.Configuration :=
  ⟨c.state.val, c.head, fun j => (c.tape j).val⟩

private theorem alternating_configuration_ext
    {c d : AlternatingNS.Machine.Configuration}
    (hs : c.state = d.state) (hh : c.head = d.head) (ht : c.tape = d.tape) : c = d := by
  cases c
  cases d
  cases hs
  cases hh
  cases ht
  rfl

theorem eraseAlternating_step {g q : ℕ}
    (M : TM0.Machine (Fin (g + 1)) (Fin (q + 1))) (c : (rapidTM0 M).Config) :
    eraseAlternating ((rapidTM0 M).nextConfig c) =
      (alternatingTM0 M).step (eraseAlternating c) := by
  by_cases hr : c.state.val < q + 1
  · have hh : (alternatingTM0 M).isHalting (eraseAlternating c) = false := by
      change decide (c.state.val = q + 1 ∨ c.state.val ∈ ([] : List ℕ)) = false
      simp only [List.not_mem_nil, or_false, decide_eq_false_iff_not, ne_of_lt hr,
        not_false_eq_true]
    have hi := alternatingTM0_instruction M ⟨c.state.val, hr⟩ (c.tape c.head)
    change (alternatingTM0 M).instruction (eraseAlternating c).state
      ((eraseAlternating c).tape (eraseAlternating c).head) = _ at hi
    simp only [AlternatingNS.Machine.step, hh, Bool.false_eq_true, ↓reduceIte]
    rw [hi]
    cases hm : M ⟨c.state.val, hr⟩ (c.tape c.head) with
    | none =>
      simp only [RapidForcing.Machine.nextConfig, rapidTM0, hr, ↓reduceDIte,
        hm, Option.map_none, eraseAlternating, AlternatingNS.Machine.states, alternatingTM0]
    | some rs =>
      rcases rs with ⟨r, s⟩
      cases s with
      | move d =>
        cases d <;>
          simp [RapidForcing.Machine.nextConfig, rapidTM0, hr, hm, eraseAlternating,
            rapidAction, encodeAction, sub_eq_add_neg, add_assoc]
      | write a =>
        simp [RapidForcing.Machine.nextConfig, rapidTM0, hr, hm, eraseAlternating,
          rapidAction, encodeAction, val_update]
  · have hs : c.state.val = q + 1 := by
      have hb : c.state.val < q + 2 := c.state.isLt
      omega
    have hh : (alternatingTM0 M).isHalting (eraseAlternating c) = true := by
      change decide (c.state.val = q + 1 ∨ c.state.val ∈ ([] : List ℕ)) = true
      simp only [hs, true_or, decide_true]
    simp only [RapidForcing.Machine.nextConfig, rapidTM0, hr, ↓reduceDIte,
      AlternatingNS.Machine.step, hh, ↓reduceIte]

theorem eraseAlternating_initial {g q : ℕ}
    (M : TM0.Machine (Fin (g + 1)) (Fin (q + 1))) (w : List (Fin (g + 1))) :
    eraseAlternating ((rapidTM0 M).initialConfig w) =
      (alternatingTM0 M).initial (w.map Fin.val) := by
  apply alternating_configuration_ext
  · rfl
  · rfl
  · funext j
    by_cases hj : 0 ≤ j
    · change (if 0 ≤ j then (w[j.toNat]?).getD (0 : Fin (g + 1)) else 0).val =
        if 0 ≤ j then ((w.map Fin.val)[j.toNat]?).getD 0 else 0
      simp only [hj, ↓reduceIte, List.getElem?_map]
      exact (Option.getD_map Fin.val (0 : Fin (g + 1)) _).symm
    · simp [eraseAlternating, RapidForcing.Machine.initialConfig,
        AlternatingNS.Machine.initial, hj, RapidForcing.Machine.blank, rapidTM0]

theorem eraseAlternating_run {g q : ℕ}
    (M : TM0.Machine (Fin (g + 1)) (Fin (q + 1))) (w : List (Fin (g + 1))) (n : ℕ) :
    eraseAlternating ((rapidTM0 M).run w n) =
      (alternatingTM0 M).run (w.map Fin.val) n := by
  induction n with
  | zero => exact eraseAlternating_initial M w
  | succ n ih =>
    have he := (eraseAlternating_step M _).trans (congrArg (alternatingTM0 M).step ih)
    simpa only [RapidForcing.Machine.run, AlternatingNS.Machine.run,
      Function.iterate_succ_apply'] using he

theorem alternatingTM0_halts_iff {g q : ℕ}
    (M : TM0.Machine (Fin (g + 1)) (Fin (q + 1))) (w : List (Fin (g + 1))) :
    (alternatingTM0 M).Halts (w.map Fin.val) ↔ (TM0.eval M w).Dom := by
  rw [← rapidTM0_halts_iff]
  change (∃ n, (alternatingTM0 M).isHalting
    ((alternatingTM0 M).run (w.map Fin.val) n) = true) ↔ _
  apply exists_congr
  intro n
  rw [← eraseAlternating_run M w n]
  change decide (((rapidTM0 M).run w n).state.val = q + 1 ∨
    ((rapidTM0 M).run w n).state.val ∈ ([] : List ℕ)) = true ↔ _
  simp only [List.not_mem_nil, or_false, decide_eq_true_eq]
  rfl

end ForcedComputation.FiniteMachine

end OAI
