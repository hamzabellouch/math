import OAI.Computability.MeanPayoff.Arithmetic

namespace OAI

section
namespace MeanPayoff.WorkStack
open BinaryStack (Op applyOp shiftOp firstWrite pendingWrite cells cells_top cells_applyOp concrete_ext)

def heads (P : Program) (code : List Bool) (c : Config P) : Fin 3 → ℤ :=
  fun k => (if k = 0 then (code.length : ℤ) else 0) - (c.stack k).length

noncomputable def canonical (P : Program) (code : List Bool) (c : Config P) :
    Configuration (machine P) := concrete P c (heads P code c)

theorem heads_update (P : Program) (code : List Bool) (c : Config P) (a : Act P.states) :
    newHeads c (heads P code c) a = heads P code ⟨some a.next, fun k => applyOp (a.work k) (c.stack k)⟩ := by
  funext k
  simp only [newHeads, heads]
  cases he : a.work k <;> cases hx : c.stack k <;>
    simp [applyOp, shiftOp, Direction.offset] <;> omega

theorem double_step_canonical (P : Program) (code : List Bool) (c : Config P) (b₁ b₂ : Bool) :
    MeanPayoff.step (machine P) (MeanPayoff.step (machine P) (canonical P code c) b₁) b₂ =
      canonical P code (step P c b₁) := by
  rcases c with ⟨q, xs⟩
  cases q with
  | none => rfl
  | some q =>
    let h := heads P code ⟨some q, xs⟩
    let top : Fin 3 → Option Bool := fun k => (xs k).head?
    have ht : (fun k => cells (xs k) (h k) (h k)) = top := by funext k; exact cells_top _ _
    cases ha : P.transition q top b₁ with
    | none =>
      change MeanPayoff.step _ (MeanPayoff.step _ (concrete P ⟨some q, xs⟩ h) b₁) b₂ = _
      simp only [MeanPayoff.step, concrete, Option.map_some, machine, decode_normal,
        ht, ha, Option.map_none]
      simp only [top] at ha
      simp only [step]; rw [ha]; rfl
    | some a =>
      change MeanPayoff.step _ (MeanPayoff.step _ (concrete P ⟨some q, xs⟩ h) b₁) b₂ = _
      simp only [MeanPayoff.step, concrete, Option.map_some, machine, decode_normal,
        ht, ha, Option.map_some, decode_pending]
      simp only [top] at ha
      simp only [step]; rw [ha]
      change _ = concrete P _ (heads P code _)
      rw [← heads_update P code ⟨some q, xs⟩ a]
      apply concrete_ext
      · rfl
      · funext k
        cases he : a.work k <;> cases hx : xs k <;> simp [concrete, newHeads, top, he, hx, shiftOp, Direction.offset, h]
      · funext k
        cases he : a.work k <;> cases hx : xs k <;>
          simpa [concrete, newHeads, top, he, hx, shiftOp, Direction.offset, h] using cells_applyOp (a.work k) (xs k) (h k)

@[simp] theorem canonical_initial (P : Program) (code : List Bool) :
    canonical P code (initial P code) = MeanPayoff.initial (machine P) code := by
  rw [concrete_initial]
  change concrete P (initial P code) (heads P code (initial P code)) = _
  congr 1
  funext k
  by_cases hk : k = 0 <;> simp [heads, initial, hk]

theorem simulate_canonical (P : Program) (code : List Bool) (bits : ℕ → Bool) (t : ℕ) :
    MeanPayoff.run (machine P) code bits (2 * t) =
      canonical P code (run P code (fun j => bits (2 * j)) t) := by
  induction t with
  | zero => exact (canonical_initial P code).symm
  | succ t ih =>
    rw [show 2 * (t + 1) = 2 * t + 1 + 1 by omega, MeanPayoff.run, MeanPayoff.run, ih,
      double_step_canonical]
    rfl

end MeanPayoff.WorkStack
namespace MeanPayoff
namespace OutputFinish
open BinaryStack (cells cells_top cells_pop cells_emit cells_end concrete_ext)
open MachineRun (advance)

def machine : Machine where
  states := 1
  start := 0
  transition _ top _ :=
    (top 0).map fun b =>
      ⟨0, ![none, top 1, some b], ![.right, .stay, .right]⟩

def state (xs ys : List Bool) (h₀ h₁ : ℤ) (t₁ : ℤ → Symbol) : Configuration machine :=
  ⟨some (0 : Fin 1), ![h₀, h₁, ys.length], ![cells xs h₀, t₁, cells ys 0]⟩
def stopped (ys : List Bool) (h₀ h₁ : ℤ) (t₁ : ℤ → Symbol) : Configuration machine :=
  ⟨none, ![h₀, h₁, ys.length], ![fun _ => none, t₁, cells ys 0]⟩

@[simp] theorem step_cons (b : Bool) (xs ys : List Bool) (h₀ h₁ : ℤ)
    (t₁ : ℤ → Symbol) (bit : Bool) :
    step machine (state (b :: xs) ys h₀ h₁ t₁) bit = state xs (ys ++ [b]) (h₀ + 1) h₁ t₁ := by
  simp only [step, state, machine, Matrix.cons_val_zero, cells_top, List.head?_cons,
    Option.map_some]
  apply concrete_ext
  · rfl
  · funext k; fin_cases k <;> simp [Direction.offset]
  · funext k; fin_cases k
    · exact (cells_pop xs b h₀).symm
    · exact Function.update_eq_self _ _
    · exact (cells_emit ys b).symm

@[simp] theorem step_nil (ys : List Bool) (h₀ h₁ : ℤ) (t₁ : ℤ → Symbol) (bit : Bool) :
    step machine (state [] ys h₀ h₁ t₁) bit = stopped ys h₀ h₁ t₁ := by
  simp [step, state, machine, stopped]

theorem copies (xs ys : List Bool) (h₀ h₁ : ℤ) (t₁ : ℤ → Symbol) (bits : ℕ → Bool) :
    advance machine bits (state xs ys h₀ h₁ t₁) (xs.length + 1) =
      stopped (ys ++ xs) (h₀ + xs.length) h₁ t₁ := by
  induction xs generalizing ys h₀ bits with
  | nil => simp [advance]
  | cons b xs ih =>
    rw [show (b :: xs).length + 1 = xs.length + 1 + 1 by simp,
      MachineRun.advance_front, step_cons, ih]
    simp [List.append_assoc, add_comm, add_left_comm]

end OutputFinish
namespace MachineRun

theorem run_after_halt (M : Machine) (code : List Bool) (bits : ℕ → Bool)
    (t u : ℕ) (ht : (run M code bits t).control = none) (hu : t ≤ u) :
    run M code bits u = run M code bits t := by
  rw [← advance_initial, show u = t + (u - t) by omega, advance_add, advance_initial,
    advance_halted M _ _ ht]

end MachineRun
namespace WorkStack
open BinaryStack (cells)

noncomputable def compiled (P : Program) : Machine :=
  MachineRun.Sequence.machine (machine P) OutputFinish.machine

theorem restart_canonical (P : Program) (code : List Bool) (c : Config P)
    (hs : c.stack 2 = []) :
    MachineRun.Sequence.restart (machine P) OutputFinish.machine (canonical P code c) =
      OutputFinish.state (c.stack 0) [] (heads P code c 0) (heads P code c 1)
        (cells (c.stack 1) (heads P code c 1)) := by
  apply BinaryStack.concrete_ext
  · rfl
  · funext k; fin_cases k <;> simp [MachineRun.Sequence.restart, canonical, concrete,
      OutputFinish.state, heads, hs]
  · funext k; fin_cases k <;> simp [MachineRun.Sequence.restart, canonical, concrete,
      OutputFinish.state, hs]

theorem compiled_run (P : Program) (code : List Bool) (bits : ℕ → Bool) (N : ℕ)
    (hh : (run P code (fun j => bits (2 * j)) N).control = none)
    (hs : (run P code (fun j => bits (2 * j)) N).stack 2 = []) :
    let out := (run P code (fun j => bits (2 * j)) N).stack 0
    let result := MeanPayoff.run (compiled P) code bits (2 * N + out.length + 1)
    result.control = none ∧ result.tape 2 = cells out 0 := by
  dsimp only
  let c := run P code (fun j => bits (2 * j)) N
  have hc : (MeanPayoff.run (machine P) code bits (2 * N)).control = none := by
    rw [simulate_canonical]; exact (concrete_halted P c _).mpr hh
  have hf := MachineRun.first_termination (machine P) bits
    (MeanPayoff.initial (machine P) code) (2 * N) (by simpa only [MachineRun.advance_initial] using hc)
  simp only [MachineRun.advance_initial] at hf
  obtain ⟨t, ht, he, ha⟩ := hf
  have hh' : (MeanPayoff.run (machine P) code bits t).control = none := by rw [he]; exact hc
  have he' : MeanPayoff.run (machine P) code bits t = canonical P code c := by
    rw [he, simulate_canonical]
  have hcopy := MachineRun.Sequence.run_after_first_halt (machine P) OutputFinish.machine
    code bits t ((c.stack 0).length + 1) ha hh'
  rw [he', restart_canonical P code c hs, OutputFinish.copies] at hcopy
  simp only [List.nil_append] at hcopy
  change MeanPayoff.run (compiled P) code bits (t + ((c.stack 0).length + 1)) = _ at hcopy
  have hstop : (MeanPayoff.run (compiled P) code bits (t + ((c.stack 0).length + 1))).control = none := by
    rw [hcopy]; rfl
  have hpad := MachineRun.run_after_halt (compiled P) code bits
    (t + ((c.stack 0).length + 1)) (2 * N + (c.stack 0).length + 1) hstop (by omega)
  change (MeanPayoff.run (compiled P) code bits (2 * N + (c.stack 0).length + 1)).control = none ∧
    (MeanPayoff.run (compiled P) code bits (2 * N + (c.stack 0).length + 1)).tape 2 = cells (c.stack 0) 0
  rw [hpad, hcopy]
  exact ⟨rfl, rfl⟩

end WorkStack
namespace PrefixCount

def front {n k : ℕ} (bits : Fin (n + k) → Bool) (j : Fin n) : Bool :=
  bits (j.castAdd k)
def back {n k : ℕ} (bits : Fin (n + k) → Bool) (j : Fin k) : Bool :=
  bits (j.natAdd n)
def concat {n k : ℕ} (p : (Fin n → Bool) × (Fin k → Bool)) (j : Fin (n + k)) : Bool :=
  if h : j.val < n then p.1 ⟨j.val, h⟩ else p.2 ⟨j.val - n, by omega⟩

@[simp] theorem front_concat {n k : ℕ} (p : (Fin n → Bool) × (Fin k → Bool)) :
    front (concat p) = p.1 := by funext j; simp [front, concat]
@[simp] theorem back_concat {n k : ℕ} (p : (Fin n → Bool) × (Fin k → Bool)) :
    back (concat p) = p.2 := by funext j; simp [back, concat]

def equiv (n k : ℕ) : ((Fin n → Bool) × (Fin k → Bool)) ≃ (Fin (n + k) → Bool) where
  toFun := concat
  invFun bits := (front bits, back bits)
  left_inv p := by simp only [front_concat, back_concat]
  right_inv bits := by
    funext j
    simp only [concat, front, back]
    split <;> rename_i hj
    · rfl
    · congr 1
      apply Fin.ext
      change n + (j.val - n) = j.val
      omega

open scoped Classical

theorem successful_count (n k : ℕ) (Q : (Fin n → Bool) → Prop) :
    (Finset.univ.filter (fun bits : Fin (n + k) → Bool => Q (front bits))).card =
      2 ^ k * (Finset.univ.filter Q).card := by
  have h := Equiv.sum_comp (equiv n k) (fun bits => if Q (front bits) then (1 : ℕ) else 0)
  rw [Fintype.sum_prod_type] at h
  simp only [equiv, Equiv.coe_fn_mk, front_concat] at h
  calc
    _ = ∑ x : Fin n → Bool, if Q x then 2 ^ k else 0 := by
      simpa [Finset.sum_boole, Fintype.card_fun] using h.symm
    _ = _ := by simp [Finset.sum_ite, Nat.mul_comm]

theorem success_transfer (n k : ℕ) (Q : (Fin n → Bool) → Prop)
    (h : 7 * 2 ^ n ≤ 8 * (Finset.univ.filter Q).card) :
    7 * 2 ^ (n + k) ≤ 8 * (Finset.univ.filter
      (fun bits : Fin (n + k) → Bool => Q (front bits))).card := by
  rw [successful_count, pow_add]
  have hh := Nat.mul_le_mul_left (2 ^ k) h
  nlinarith only [hh]

theorem two_phase_success (n k : ℕ) (Q : (Fin n → Bool) → Prop)
    (h : 7 * 2 ^ n ≤ 8 * (Finset.univ.filter Q).card) :
    7 * 2 ^ (2 * n + k) ≤ 8 * (Finset.univ.filter
      (fun bits : Fin (2 * n + k) → Bool => Q (TwoPhase.even (front bits)))).card :=
  success_transfer (2 * n) k _ (TwoPhase.success_transfer n Q h)

end PrefixCount
namespace WorkStack

theorem run_congr (P : Program) (code : List Bool) (a b : ℕ → Bool) (N : ℕ)
    (h : ∀ j < N, a j = b j) : run P code a N = run P code b N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    change step P (run P code a N) (a N) = step P (run P code b N) (b N)
    rw [ih (fun j hj => h j (by omega)), h N (by omega)]

theorem prefix_even_run (P : Program) (code : List Bool) (N k : ℕ)
    (bits : Fin (2 * N + k) → Bool) :
    run P code (fun j => padBits bits (2 * j)) N =
      run P code (padBits (TwoPhase.even (PrefixCount.front bits))) N := by
  apply run_congr
  intro j hj
  simp only [padBits, show 2 * j < 2 * N + k by omega, hj, ↓reduceDIte,
    TwoPhase.even, PrefixCount.front]
  rfl

end WorkStack
end MeanPayoff
namespace MeanPayoff
namespace WorkStack
open BinaryStack (cells)

def Ready (P : Program) (code : List Bool) (N E : ℕ) : Prop :=
  ∀ bits : Fin N → Bool, let c := run P code (padBits bits) N
    c.control = none ∧ c.stack 2 = [] ∧ (c.stack 0).length = E

def output (P : Program) (code : List Bool) (N : ℕ) (bits : Fin N → Bool) : List Bool :=
  (run P code (padBits bits) N).stack 0

theorem compiled_packet (P : Program) (code : List Bool) (N E : ℕ)
    (hr : Ready P code N E) (bits : Fin (2 * N + (E + 1)) → Bool) :
    let c := MeanPayoff.run (compiled P) code (padBits bits) (2 * N + (E + 1))
    let out := output P code N (TwoPhase.even (PrefixCount.front bits))
    c.control = none ∧ c.tape 2 = cells out 0 := by
  let short := TwoPhase.even (PrefixCount.front bits)
  obtain ⟨hh, hs, hl⟩ := hr short
  have he := prefix_even_run P code N (E + 1) bits
  have hh' : (run P code (fun j => padBits bits (2 * j)) N).control = none := by rw [he]; exact hh
  have hs' : (run P code (fun j => padBits bits (2 * j)) N).stack 2 = [] := by rw [he]; exact hs
  have h := compiled_run P code (padBits bits) N hh' hs'
  dsimp only at h ⊢
  rw [he] at h
  change ((run P code (padBits short) N).stack 0).length = E at hl
  dsimp only [short] at hl
  rw [hl, Nat.add_assoc] at h
  exact h

open scoped Classical

theorem compiled_success (P : Program) (code : List Bool) (N E : ℕ)
    (hr : Ready P code N E) (Q : List Bool → Prop)
    (hs : 7 * 2 ^ N ≤ 8 * (Finset.univ.filter
      (fun bits : Fin N → Bool => Q (output P code N bits))).card) :
    7 * 2 ^ (2 * N + (E + 1)) ≤ 8 * (Finset.univ.filter
      (fun bits : Fin (2 * N + (E + 1)) → Bool =>
        ∃ out, Q out ∧
          (MeanPayoff.run (compiled P) code (padBits bits) (2 * N + (E + 1))).control = none ∧
          (MeanPayoff.run (compiled P) code (padBits bits) (2 * N + (E + 1))).tape 2 = cells out 0)).card := by
  have h := PrefixCount.two_phase_success N (E + 1) (fun bits => Q (output P code N bits)) hs
  apply h.trans
  apply Nat.mul_le_mul_left
  apply Finset.card_le_card
  intro bits hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
  exact ⟨output P code N (TwoPhase.even (PrefixCount.front bits)), hb,
    compiled_packet P code N E hr bits⟩

end WorkStack

theorem correctList_packet (G : Game) (M : Machine) (c : Configuration M) (out : List Bool)
    (h : BinaryInput.CorrectList G out) (hh : c.control = none)
    (ht : c.tape 2 = BinaryStack.cells out 0) : CorrectOutput G c := by
  refine ⟨hh, ?_, ?_, ?_⟩
  · intro v
    rw [ht]
    simpa only [BinaryStack.cells, sub_zero, Int.natCast_nonneg, ↓reduceIte,
      Int.toNat_natCast] using h.2 v
  · intro v
    have hv : v.val < out.length := by rw [h.1]; exact v.isLt
    have he : out[v.val]? = some out[v.val] := List.getElem?_eq_getElem hv
    have hc := h.2 v
    rw [he, Option.some.injEq] at hc
    rw [ht]
    simp only [BinaryStack.cells, sub_zero, Int.natCast_nonneg, ↓reduceIte,
      Int.toNat_natCast, he, Option.some.injEq, ← hc]
    cases out[v.val] <;> simp
  · intro j hj
    rw [ht]
    apply BinaryStack.cells_outside
    simpa only [h.1] using hj

end MeanPayoff
end

end OAI
