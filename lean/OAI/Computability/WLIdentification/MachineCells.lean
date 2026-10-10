import OAI.Computability.WLIdentification.CellularCircuits

namespace OAI

namespace WLIdentification

namespace Machine

abbrev State (M : Machine) := Fin (M.extraStates + 3)
abbrev Symbol (M : Machine) := Fin (M.extraSymbols + 3)
abbrev Letter (M : Machine) := M.Symbol × Option M.State

/-- Extend the finite transition table by its stipulated frozen halts. -/
def action (M : Machine) (q : M.State) (a : M.Symbol) : M.State × M.Symbol × Move :=
  if q = 1 ∨ q = 2 then (q, a, .stay) else M.transition q a

@[simp] theorem action_halt (M : Machine) (q : M.State) (a : M.Symbol)
    (h : q = 1 ∨ q = 2) : M.action q a = (q, a, .stay) := ite_eq_left h

/-- A completely fixed radius-one alphabet table. The arbitrary multihead cases
are settled by center, then left, then right priority. -/
def localRule (M : Machine) (a b c : M.Letter) : M.Letter :=
  let written := match b.2 with
    | none => b.1
    | some q => (M.action q b.1).2.1
  let head := match b.2 with
    | some q => if (M.action q b.1).2.2 = .stay then some (M.action q b.1).1 else none
    | none => match a.2 with
      | some q => if (M.action q a.1).2.2 = .right then some (M.action q a.1).1 else
          match c.2 with
          | none => none
          | some q => if (M.action q c.1).2.2 = .left then some (M.action q c.1).1 else none
      | none => match c.2 with
        | none => none
        | some q => if (M.action q c.1).2.2 = .left then some (M.action q c.1).1 else none
  (written, head)

/-- The same head/tape representation on any cyclic position alphabet. -/
structure TapeConfig (M : Machine) (X : Type) where
  state : M.State
  head : X
  tape : X → M.Symbol

namespace TapeConfig
variable {M : Machine} {X : Type} [DecidableEq X]

def letter (c : M.TapeConfig X) (x : X) : M.Letter :=
  (c.tape x, if x = c.head then some c.state else none)

def advance (e : X ≃ X) (c : M.TapeConfig X) : M.TapeConfig X :=
  let a := M.action c.state (c.tape c.head)
  { state := a.1
    head := match a.2.2 with
      | .left => e.symm c.head
      | .stay => c.head
      | .right => e c.head
    tape := Function.update c.tape c.head a.2.1 }

/-- The finite local table is an actual one-head machine step, including seam
crossings and halted configurations; no cellular-automaton theorem is assumed. -/
theorem localRule_correct (e : X ≃ X)
    (hfix : ∀ x, e x ≠ x) (htwo : ∀ x, e x ≠ e.symm x)
    (c : M.TapeConfig X) (x : X) :
    M.localRule (c.letter (e.symm x)) (c.letter x) (c.letter (e x)) =
      (c.advance e).letter x := by
  have hfix' (x : X) : e.symm x ≠ x := by
    intro h
    have he := congrArg e h
    exact hfix x (by simpa using he.symm)
  have hL : e.symm x = c.head ↔ x = e c.head := e.symm_apply_eq
  have hR : e x = c.head ↔ x = e.symm c.head := e.eq_symm_apply.symm
  by_cases hc : x = c.head
  · subst x
    have hl := hfix' c.head
    have hr := hfix c.head
    cases hm : (M.action c.state (c.tape c.head)).2.2 <;>
      simp [localRule, letter, advance, hm, Ne.symm hl, Ne.symm hr]
  · by_cases hl : e.symm x = c.head
    · have hr : e x ≠ c.head := by intro he; exact htwo x (he.trans hl.symm)
      have hx := hL.mp hl
      simp only [localRule, letter, hc, hl, hr, ite_true, ite_false]
      cases hm : (M.action c.state (c.tape c.head)).2.2 <;>
        simp [advance, hm, hx, hfix, htwo]
    · by_cases hr : e x = c.head
      · have hx := hR.mp hr
        simp only [localRule, letter, hc, hl, hr, ite_true, ite_false]
        cases hm : (M.action c.state (c.tape c.head)).2.2 <;>
          simp [advance, hm, hx, hfix', Ne.symm (htwo c.head)]
      · cases hm : (M.action c.state (c.tape c.head)).2.2 <;>
          simp [localRule, letter, advance, hm, hc, hl, hr, ← hL, ← hR]

theorem advance_halted (e : X ≃ X) (c : M.TapeConfig X)
    (h : c.state = 1 ∨ c.state = 2) : c.advance e = c := by
  simp only [advance, action_halt M _ _ h]
  cases c
  simp

end TapeConfig

/-- The literal input convention, transferred to a finite line segment. -/
def ringInitial (M : Machine) {d : ℕ} (w : Word) : M.TapeConfig (BinaryAddress.Bits d) where
  state := 0
  head := fun _ => false
  tape j := (w[BinaryAddress.value j]?).elim 0 (inputSymbol M)

noncomputable def ringRun (M : Machine) {d : ℕ} (w : Word) (t : ℕ) :
    M.TapeConfig (BinaryAddress.Bits d) :=
  (TapeConfig.advance (BinaryAddress.rotation d))^[t] (M.ringInitial w)

end Machine

namespace Machine
open BinaryAddress

/-- The literal bounded input segment, with one head marker. -/
abbrev inputSpan (w : Word) := max 1 w.length

abbrev InitialSeed (d : ℕ) (w : Word) := Fin (inputSpan w) ⊕ ThresholdCase (ofNat d (inputSpan w))

def initialSeedLetter (M : Machine) (d : ℕ) (w : Word) : InitialSeed d w → M.Letter
  | .inl i => ((M.ringInitial w).letter (ofNat d i.val))
  | .inr _ => (0, none)

def initialSeedMap (d : ℕ) (w : Word) : InitialSeed d w → ProductMap d
  | .inl i => ProductMap.singleton (ofNat d i.val) (ofNat d i.val)
  | .inr h => thresholdMap (ofNat d (inputSpan w)) h

theorem ringInitial_blank (M : Machine) {d : ℕ} (w : Word) (x : Bits d)
    (hx : inputSpan w ≤ value x) : (M.ringInitial w).letter x = (0, none) := by
  have hn : w.length ≤ value x := (le_max_right _ _).trans hx
  have h0 : x ≠ fun _ => false := by
    intro he
    rw [he, value_zero] at hx
    exact Nat.not_succ_le_zero 0 ((le_max_left 1 w.length).trans hx)
  simp only [TapeConfig.letter, ringInitial, h0, ite_false]
  rw [List.getElem?_eq_none (by omega)]
  rfl

theorem initialSeed_correct (M : Machine) {d : ℕ} (w : Word)
    (hsize : inputSpan w < 2 ^ d) :
    CellularCircuit.SeedCorrect (M.initialSeedLetter d w) (initialSeedMap d w)
      (M.ringInitial w).letter := by
  intro f x
  constructor
  · rintro ⟨z, y, rfl, hz⟩
    cases z with
    | inl i =>
      obtain ⟨rfl, _⟩ := (ProductMap.singleton_rel _ _ _ _).mp hz
      rfl
    | inr h =>
      have hs := (threshold_sound _ h hz).1
      rw [value_ofNat _ _ hsize] at hs
      exact (ringInitial_blank M w x hs).symm
  · intro hf
    by_cases hx : value x < inputSpan w
    · let i : Fin (inputSpan w) := ⟨value x, hx⟩
      refine ⟨.inl i, x, ?_, ?_⟩
      · simp only [initialSeedLetter, i, ofNat_value, hf]
      · change (ProductMap.singleton (ofNat d (value x)) (ofNat d (value x))).Rel x x
        simp only [ofNat_value, ProductMap.singleton_rel, and_self]
    · have hle : inputSpan w ≤ value x := by omega
      obtain ⟨h, hh⟩ := threshold_complete (ofNat d (inputSpan w)) x
        (by simpa only [value_ofNat _ _ hsize] using hle)
      refine ⟨.inr h, x, ?_, hh⟩
      exact (ringInitial_blank M w x hle).symm.trans hf.symm

/-- The concrete compressed tableau, now with no semantic seed assumption. -/
noncomputable abbrev compiledCircuit (M : Machine) (d : ℕ) (w : Word) :=
  { CellularCircuit.circuit M.localRule (M.initialSeedLetter d w) (initialSeedMap d w)
    (fun a => a.2 = some 1) with
    seedIndex := NaturalCode.sum (NaturalCode.fin (inputSpan w))
      (NaturalCode.option (NaturalCode.subtype (NaturalCode.fin d) _)) }

theorem compiledCircuit_iff (M : Machine) {d : ℕ} (w : Word)
    (hsize : inputSpan w < 2 ^ d) : (M.compiledCircuit d w).Accepted ↔
    ∃ j : Bits d,
      (CellularCircuit.evolution M.localRule (M.ringInitial w).letter (2 ^ d - 1) j).2 = some 1 :=
  (ProductCircuit.accepted_reseed _ _).trans
    (CellularCircuit.accepted_iff M.localRule _ _ (fun a => a.2 = some 1) _
      (M.initialSeed_correct w hsize))

end Machine

namespace BinaryAddress

theorem value_rotation {d : ℕ} (x : Bits d) :
    value (rotation d x) = if value x + 1 < 2 ^ d then value x + 1 else 0 := by
  rw [rotation_advance, advance_mod]
  have hx := value_lt x
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · have he : value x + 1 = 2 ^ d := by omega
    rw [he, Nat.mod_self]

theorem rotation_ne_self {d : ℕ} (hd : 1 < 2 ^ d) (x : Bits d) : rotation d x ≠ x := by
  intro h
  have he := congrArg value h
  rw [value_rotation] at he
  have hx := value_lt x
  split_ifs at he <;> omega

theorem rotation_ne_symm {d : ℕ} (hd : 2 < 2 ^ d) (x : Bits d) :
    rotation d x ≠ (rotation d).symm x := by
  intro h
  have he := congrArg (rotation d) h
  rw [Equiv.apply_symm_apply] at he
  have hv := congrArg value he
  rw [value_rotation, value_rotation] at hv
  have hx := value_lt x
  split_ifs at hv <;> omega

end BinaryAddress

namespace Machine
open BinaryAddress

@[simp] theorem ringRun_zero (M : Machine) {d : ℕ} (w : Word) :
    @ringRun M d w 0 = M.ringInitial w := rfl

@[simp] theorem ringRun_succ (M : Machine) {d : ℕ} (w : Word) (t : ℕ) :
    @ringRun M d w (t + 1) = (M.ringRun w t).advance (rotation d) :=
  Function.iterate_succ_apply' _ _ _

theorem evolution_ringRun (M : Machine) {d : ℕ} (hd : 2 < 2 ^ d) (w : Word) (t : ℕ) :
    CellularCircuit.evolution M.localRule (M.ringInitial w).letter t =
      (@ringRun M d w t).letter := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext j
    simp only [CellularCircuit.evolution, ih, ringRun_succ]
    exact TapeConfig.localRule_correct (rotation d) (rotation_ne_self (by omega))
      (rotation_ne_symm hd) _ _

theorem exists_letter_accept {M : Machine} {X : Type} [DecidableEq X]
    (c : M.TapeConfig X) : (∃ x, (c.letter x).2 = some 1) ↔ c.state = 1 := by
  constructor
  · rintro ⟨x, hx⟩
    change (if x = c.head then some c.state else none) = some 1 at hx
    split_ifs at hx with he
    exact Option.some.inj hx
  · intro h
    exact ⟨c.head, by simp [TapeConfig.letter, h]⟩

theorem compiledCircuit_ringRun (M : Machine) {d : ℕ} (hd : 2 < 2 ^ d)
    (w : Word) (hsize : inputSpan w < 2 ^ d) :
    (M.compiledCircuit d w).Accepted ↔ (@ringRun M d w (2 ^ d - 1)).state = 1 := by
  rw [compiledCircuit_iff M w hsize, evolution_ringRun M hd w]
  exact exists_letter_accept _

end Machine

namespace BinaryAddress

def residue (d : ℕ) (z : ℤ) : Bits d := ofNat d (z % (2 ^ d : ℕ)).toNat

theorem value_residue (d : ℕ) (z : ℤ) : value (residue d z) = (z % (2 ^ d : ℕ)).toNat := by
  apply value_ofNat
  exact (Int.toNat_lt (Int.emod_nonneg _ (by positivity))).mpr
    (Int.emod_lt_of_pos _ (by positivity))

@[simp] theorem residue_zero (d : ℕ) : residue d 0 = fun _ => false := by
  simp [residue]

theorem residue_add_one (d : ℕ) (z : ℤ) : residue d (z + 1) = rotation d (residue d z) := by
  apply value_injective d
  rw [value_residue, rotation_advance, advance_mod, value_residue]
  apply Int.ofNat_inj.mp
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity)), Int.natCast_emod,
    Nat.cast_add, Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity)), Nat.cast_one]
  simp only [Int.add_emod, Int.emod_emod]

theorem residue_sub_one (d : ℕ) (z : ℤ) : residue d (z - 1) = (rotation d).symm (residue d z) := by
  apply (rotation d).injective
  rw [Equiv.apply_symm_apply, ← residue_add_one]
  congr 1
  omega

theorem residue_injective_window {d T : ℕ} (hsize : 2 * T < 2 ^ d) {x y : ℤ}
    (hx : -(T : ℤ) ≤ x ∧ x ≤ T) (hy : -(T : ℤ) ≤ y ∧ y ≤ T)
    (h : residue d x = residue d y) : x = y := by
  have hv := congrArg value h
  rw [value_residue, value_residue] at hv
  have he : x % (2 ^ d : ℕ) = y % (2 ^ d : ℕ) := by
    have hc := congrArg (fun n : ℕ => (n : ℤ)) hv
    simpa only [Int.toNat_of_nonneg (Int.emod_nonneg x (b := (2 ^ d : ℕ)) (by positivity)),
      Int.toNat_of_nonneg (Int.emod_nonneg y (b := (2 ^ d : ℕ)) (by positivity))] using hc
  have hh := (Int.emod_add_cancel_right (m := x) (k := y) (n := (2 ^ d : ℕ)) (i := T)).mpr he
  have hx0 : 0 ≤ x + T := by omega
  have hy0 : 0 ≤ y + T := by omega
  have hxlt : x + T < (2 ^ d : ℕ) := by omega
  have hylt : y + T < (2 ^ d : ℕ) := by omega
  rw [Int.emod_eq_of_lt hx0 hxlt, Int.emod_eq_of_lt hy0 hylt] at hh
  omega

theorem value_residue_of_nonneg {d : ℕ} {z : ℤ} (h0 : 0 ≤ z) (hlt : z < (2 ^ d : ℕ)) :
    value (residue d z) = z.toNat := by rw [value_residue, Int.emod_eq_of_lt h0 hlt]

theorem value_residue_negative {d : ℕ} {z : ℤ} (hlt : -(2 ^ d : ℕ) < z) (h0 : z < 0) :
    (value (residue d z) : ℤ) = z + (2 ^ d : ℕ) := by
  rw [value_residue, Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))]
  have h := (Int.ediv_emod_unique (a := z) (b := (2 ^ d : ℕ))
    (q := -1) (r := z + (2 ^ d : ℕ)) (by positivity)).mpr (by constructor <;> omega)
  exact h.2

end BinaryAddress

end WLIdentification

end OAI
