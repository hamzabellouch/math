import OAI.MathematicalPhysics.NavierStokes.Material.Machines

namespace OAI

/-! The finite integer arithmetic of the periodic-lattice processor. A
configuration uses two fixed-width stacks and one state digit. Every integer
address is decoded by its least nonnegative residue, including negative lifts
of the same point on the torus. -/

namespace ForcedComputation.Lattice

def stackBase (b d : ℕ) : ℕ := b ^ d

def period (b d : ℕ) : ℕ := b ^ (2 * d + 1)

def pack (b d L R q : ℕ) : ℕ := L + stackBase b d * (R + stackBase b d * q)

def leftStack (b d c : ℕ) : ℕ := c % stackBase b d

def rightStack (b d c : ℕ) : ℕ := (c / stackBase b d) % stackBase b d

def stateDigit (b d c : ℕ) : ℕ := (c / stackBase b d) / stackBase b d

theorem stackBase_pos {b : ℕ} (hb : 0 < b) (d : ℕ) : 0 < stackBase b d :=
  pow_pos hb d

theorem period_pos {b : ℕ} (hb : 0 < b) (d : ℕ) : 0 < period b d :=
  pow_pos hb _

theorem period_eq (b d : ℕ) : period b d = stackBase b d * stackBase b d * b := by
  simp only [period, stackBase, two_mul, pow_add, pow_one]

theorem prepend_lt {b B a t : ℕ} (ha : a < b) (ht : t < B) : a + b * t < b * B := by
  nlinarith

theorem pack_lt {b d L R q : ℕ} (hL : L < stackBase b d)
    (hR : R < stackBase b d) (hq : q < b) : pack b d L R q < period b d := by
  rw [period_eq]
  simpa only [pack, Nat.mul_assoc] using prepend_lt hL (prepend_lt hR hq)

theorem pack_left {b d L R q : ℕ} (hL : L < stackBase b d) :
    leftStack b d (pack b d L R q) = L := by
  simp only [leftStack, pack, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hL]

theorem pack_div {b d L R q : ℕ} (hb : 0 < b) (hL : L < stackBase b d) :
    pack b d L R q / stackBase b d = R + stackBase b d * q := by
  rw [pack, Nat.add_mul_div_left _ _ (stackBase_pos hb d), Nat.div_eq_of_lt hL,
    Nat.zero_add]

theorem pack_right {b d L R q : ℕ} (hb : 0 < b) (hL : L < stackBase b d)
    (hR : R < stackBase b d) : rightStack b d (pack b d L R q) = R := by
  rw [rightStack, pack_div hb hL]
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hR]

theorem pack_state {b d L R q : ℕ} (hb : 0 < b) (hL : L < stackBase b d)
    (hR : R < stackBase b d) : stateDigit b d (pack b d L R q) = q := by
  rw [stateDigit, pack_div hb hL,
    Nat.add_mul_div_left _ _ (stackBase_pos hb d), Nat.div_eq_of_lt hR, Nat.zero_add]

theorem leftStack_lt {b : ℕ} (hb : 0 < b) (d c : ℕ) :
    leftStack b d c < stackBase b d := Nat.mod_lt _ (stackBase_pos hb d)

theorem rightStack_lt {b : ℕ} (hb : 0 < b) (d c : ℕ) :
    rightStack b d c < stackBase b d := Nat.mod_lt _ (stackBase_pos hb d)

theorem stateDigit_lt {b d c : ℕ} (hb : 0 < b) (hc : c < period b d) :
    stateDigit b d c < b := by
  unfold stateDigit
  apply (Nat.div_lt_iff_lt_mul (stackBase_pos hb d)).mpr
  apply (Nat.div_lt_iff_lt_mul (stackBase_pos hb d)).mpr
  rw [period_eq] at hc
  simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hc

theorem pack_decode (b d c : ℕ) :
    pack b d (leftStack b d c) (rightStack b d c) (stateDigit b d c) = c := by
  unfold pack leftStack rightStack stateDigit
  rw [Nat.mod_add_div, Nat.mod_add_div]

def address (b d : ℕ) (j : ℤ) : ℕ := j.natMod (period b d)

theorem address_lt {b : ℕ} (hb : 0 < b) (d : ℕ) (j : ℤ) :
    address b d j < period b d := Int.natMod_lt (Nat.ne_of_gt (period_pos hb d))

theorem address_periodic (b d : ℕ) :
    Function.Periodic (address b d) (period b d : ℤ) := by
  intro j
  simp only [address, Int.natMod, Int.add_emod_right]

theorem address_nat {b d c : ℕ} (hc : c < period b d) : address b d (c : ℤ) = c := by
  simp only [address, Int.natMod, ← Int.natCast_mod, Int.toNat_natCast,
    Nat.mod_eq_of_lt hc]

theorem address_congr {b d : ℕ} {i j : ℤ}
    (h : i % (period b d : ℤ) = j % (period b d : ℤ)) :
    address b d i = address b d j := congrArg Int.toNat h

/-- Move 0 is left, move 1 is stationary, and move 2 is right. -/
def nextLeft (b L a : ℕ) (m : Fin 3) : ℕ :=
  if m = 0 then L / b else if m = 1 then L else a + b * L

def nextRight (b L R a : ℕ) (m : Fin 3) : ℕ :=
  if m = 0 then L % b + b * (a + b * (R / b))
  else if m = 1 then a + b * (R / b) else R / b

theorem left_move_formula (b L R a : ℕ) :
    nextRight b L R a 0 = L % b + b * a + b * (R - R % b) := by
  have h := Nat.mod_add_div R b
  have hs : R - R % b = b * (R / b) := by omega
  norm_num [nextRight, Fin.ext_iff]
  rw [hs]
  ring

theorem stationary_move_formula (b L R a : ℕ) :
    nextRight b L R a 1 = R - R % b + a := by
  have h := Nat.mod_add_div R b
  have hs : R - R % b = b * (R / b) := by omega
  norm_num [nextRight, Fin.ext_iff]
  rw [hs, Nat.add_comm]

theorem quotient_power_lt {b d R : ℕ} (hb : 0 < b) (hd : 0 < d)
    (hR : R < b ^ d) : R / b < b ^ (d - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  apply (Nat.div_lt_iff_lt_mul hb).mpr
  simpa only [pow_succ, Nat.succ_sub_one] using hR

theorem next_stacks_lt {b d L R a : ℕ} (hb : 2 ≤ b) (hd : 0 < d)
    (hL : L < stackBase b d) (hR : R < stackBase b d) (ha : a < b)
    (m : Fin 3) :
    nextLeft b L a m < b ^ (d + 1) ∧ nextRight b L R a m < b ^ (d + 1) := by
  have hb₀ : 0 < b := by omega
  have hpow : b ^ d ≤ b ^ (d + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hq : R / b < b ^ (d - 1) := quotient_power_lt hb₀ hd hR
  have hp : a + b * (R / b) < b ^ d := by
    have hp := prepend_lt ha hq
    have he : b * b ^ (d - 1) = b ^ d := by
      rw [← pow_succ']
      congr 1
      omega
    rwa [he] at hp
  fin_cases m
  · norm_num [nextLeft, nextRight, Fin.ext_iff]
    refine ⟨(Nat.div_le_self L b).trans_lt (hL.trans_le hpow), ?_⟩
    simpa only [pow_succ, Nat.mul_comm] using
      (prepend_lt (Nat.mod_lt L hb₀) hp)
  · norm_num [nextLeft, nextRight, Fin.ext_iff]
    exact ⟨hL.trans_le hpow, hp.trans_le hpow⟩
  · norm_num [nextLeft, nextRight, Fin.ext_iff]
    exact ⟨by simpa only [stackBase, pow_succ, Nat.mul_comm] using prepend_lt ha hL,
      (Nat.div_le_self R b).trans_lt (hR.trans_le hpow)⟩

structure Rule (b : ℕ) where
  next : Fin b
  write : Fin b
  move : Fin 3
  deriving DecidableEq

/-- A finite lookup table, without any assumption about addresses visited by a run. -/
structure Table (b : ℕ) where
  rows : List (List (Option (Rule b)))
  halting : List ℕ
  deriving DecidableEq

def Table.lookup {b : ℕ} (T : Table b) (q a : ℕ) : Option (Rule b) :=
  ((T.rows[q]?).bind fun row => row[a]?).join

def readTransition {b : ℕ} (T : Table b) (d c : ℕ) : ℕ :=
  match T.lookup (stateDigit b d c) (rightStack b d c % b) with
  | none => 0
  | some r => pack b (d + 2)
      (nextLeft b (leftStack b d c) r.write r.move)
      (nextRight b (leftStack b d c) (rightStack b d c) r.write r.move) r.next

def transition {b : ℕ} (T : Table b) (d : ℕ) (j : ℤ) : ℕ :=
  readTransition T d (address b d j)

def haltFlag {b : ℕ} (T : Table b) (d : ℕ) (j : ℤ) : Bool :=
  decide (stateDigit b d (address b d j) ∈ T.halting)

theorem transition_periodic {b : ℕ} (T : Table b) (d : ℕ) :
    Function.Periodic (transition T d) (period b d : ℤ) := by
  intro j
  unfold transition
  rw [address_periodic b d j]

theorem haltFlag_periodic {b : ℕ} (T : Table b) (d : ℕ) :
    Function.Periodic (haltFlag T d) (period b d : ℤ) := by
  intro j
  unfold haltFlag
  rw [address_periodic b d j]

theorem readTransition_lt {b : ℕ} (T : Table b) (hb : 2 ≤ b) {d c : ℕ}
    (hd : 0 < d) (_hc : c < period b d) : readTransition T d c < period b (d + 2) := by
  have hb₀ : 0 < b := by omega
  unfold readTransition
  split
  · exact period_pos hb₀ _
  · rename_i r _
    have hp := next_stacks_lt hb hd (leftStack_lt hb₀ d c)
      (rightStack_lt hb₀ d c) r.write.isLt r.move
    have hs : b ^ (d + 1) ≤ stackBase b (d + 2) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    exact pack_lt (hp.1.trans_le hs) (hp.2.trans_le hs) r.next.isLt

theorem transition_lt {b : ℕ} (T : Table b) (hb : 2 ≤ b) {d : ℕ}
    (hd : 0 < d) (j : ℤ) : transition T d j < period b (d + 2) :=
  readTransition_lt T hb hd (address_lt (by omega) d j)

theorem readTransition_pack {b : ℕ} (T : Table b) (hb : 0 < b)
    {d L R q : ℕ} (hL : L < stackBase b d) (hR : R < stackBase b d) {r : Rule b}
    (hr : T.lookup q (R % b) = some r) :
    readTransition T d (pack b d L R q) =
      pack b (d + 2) (nextLeft b L r.write r.move) (nextRight b L R r.write r.move) r.next := by
  simp only [readTransition, pack_state hb hL hR, pack_right hb hL hR,
    pack_left hL, hr]

end ForcedComputation.Lattice

end OAI
