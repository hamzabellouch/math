import OAI.Analysis.PeriodicLattice.Scales

namespace OAI

/-! Machine histories, encoded stacks and the open particle detector. -/

namespace PeriodicLattice

local instance finiteFunctionEncodingMachines {n : ℕ} {A : Type*} [Encodable A] :
    Encodable (Fin n → A) := Encodable.finArrow

noncomputable section

namespace History

open Scales

def address (b L : ℕ) (c : ℕ → ℕ) (n : ℕ) : ℕ :=
  (∑ k ∈ Finset.range n, b ^ (exponent L n - exponent L k) * c k) + c n

def coordinate (b L : ℕ) (c : ℕ → ℕ) (n : ℕ) : ℝ :=
  1 / 2 + ∑ k ∈ Finset.range (n + 1), epsilon b L k * (c k : ℝ)

theorem epsilon_ratio {b : ℕ} (hb : 2 ≤ b) (L : ℕ) {k n : ℕ} (hkn : k ≤ n) :
    epsilon b L k / epsilon b L n = (b : ℝ) ^ (exponent L n - exponent L k) := by
  unfold epsilon
  rw [inv_div_inv, div_eq_mul_inv]
  exact (pow_sub₀ _ (by exact_mod_cast (by omega : b ≠ 0))
    ((exponent_strictMono L).monotone hkn)).symm

theorem read_coordinate {b : ℕ} (hb : 2 ≤ b) (L : ℕ) (c : ℕ → ℕ) (n : ℕ) :
    (coordinate b L c n - 1 / 2) / epsilon b L n = (address b L c n : ℝ) := by
  unfold coordinate address
  rw [add_sub_cancel_left, Finset.sum_range_succ, add_div]
  simp only [Nat.cast_add, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow]
  rw [Finset.sum_div]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    rw [mul_div_right_comm, epsilon_ratio hb L (Nat.le_of_lt (Finset.mem_range.mp hk))]
  · have he : epsilon b L n ≠ 0 := (epsilon_pos hb L n).ne'
    field_simp

theorem read_residue (b L : ℕ) (c : ℕ → ℕ) (n : ℕ)
    (hc : c n < capacity b L n) :
    address b L c n % capacity b L n = c n := by
  have hd : capacity b L n ∣
      ∑ k ∈ Finset.range n, b ^ (exponent L n - exponent L k) * c k := by
    apply Finset.dvd_sum
    intro k hk
    exact dvd_mul_of_dvd_left (capacity_dvd_scaleRatio b L (Finset.mem_range.mp hk)) _
  rw [address, Nat.add_mod, Nat.dvd_iff_mod_eq_zero.mp hd,
    zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hc]

theorem lift_invariant_residue (b L : ℕ) (c : ℕ → ℕ) (n : ℕ)
    (hc : c n < capacity b L n) (z : ℤ) :
    ((address b L c n : ℤ) + z * (b ^ exponent L n : ℕ)) % (capacity b L n : ℤ) =
      (c n : ℤ) := by
  have hd : (capacity b L n : ℤ) ∣ z * (b ^ exponent L n : ℕ) := by
    apply dvd_mul_of_dvd_right
    exact_mod_cast capacity_dvd_inverseScale b L n
  have hr : (address b L c n : ℤ) % (capacity b L n : ℤ) = (c n : ℤ) := by
    exact_mod_cast read_residue b L c n hc
  rw [Int.add_emod, Int.emod_eq_zero_of_dvd hd, add_zero, Int.emod_emod, hr]

theorem read_any_lift {b : ℕ} (hb : 2 ≤ b) (L : ℕ) (c : ℕ → ℕ) (n : ℕ)
    (hc : c n < capacity b L n) (z : ℤ) :
    ∃ j : ℤ,
      (coordinate b L c n + (z : ℝ) - 1 / 2) / epsilon b L n = (j : ℝ) ∧
      j % (capacity b L n : ℤ) = c n := by
  refine ⟨(address b L c n : ℤ) + z * (b ^ exponent L n : ℕ), ?_,
    lift_invariant_residue b L c n hc z⟩
  rw [show coordinate b L c n + (z : ℝ) - 1 / 2 =
      (coordinate b L c n - 1 / 2) + z by ring, add_div, read_coordinate hb]
  push_cast
  simp [epsilon, div_eq_mul_inv]

end History

namespace StackCode

structure Code where
  left : ℕ
  right : ℕ
  state : ℕ
  deriving DecidableEq

def pack (b d : ℕ) (c : Code) : ℕ :=
  c.left + b ^ d * (c.right + b ^ d * c.state)

def unpackNat (b d c : ℕ) : Code where
  left := c % b ^ d
  right := c / b ^ d % b ^ d
  state := c / b ^ d / b ^ d

def residue (b d : ℕ) (j : ℤ) : ℕ := (j % (b ^ (2 * d + 1) : ℕ)).toNat

def unpack (b d : ℕ) (j : ℤ) : Code := unpackNat b d (residue b d j)

theorem pack_eq (b d : ℕ) (c : Code) :
    pack b d c = c.left + b ^ d * c.right + b ^ (2 * d) * c.state := by
  rw [pack, mul_add, pow_mul, sq]
  ring

theorem pack_lt {b d : ℕ} (hb : 2 ≤ b) (c : Code)
    (hl : c.left < b ^ d) (hr : c.right < b ^ d) (hs : c.state < b) :
    pack b d c < b ^ (2 * d + 1) := by
  have hp : 0 < b ^ d := pow_pos (by omega : 0 < b) _
  have h1 : c.right + b ^ d * c.state < b ^ d * b := by
    have hm := Nat.mul_le_mul_left (b ^ d) (Nat.succ_le_of_lt hs)
    nlinarith
  have h2 := Nat.mul_le_mul_left (b ^ d) (Nat.succ_le_of_lt h1)
  rw [pack, show 2 * d + 1 = d * 2 + 1 by omega, pow_succ, pow_mul, sq]
  nlinarith

theorem unpackNat_pack {b d : ℕ} (hb : 2 ≤ b) (c : Code)
    (hl : c.left < b ^ d) (hr : c.right < b ^ d) :
    unpackNat b d (pack b d c) = c := by
  have hp : 0 < b ^ d := pow_pos (by omega : 0 < b) _
  simp [unpackNat, pack, Nat.add_mul_div_left, Nat.div_eq_of_lt hl,
    Nat.div_eq_of_lt hr, Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hr, hp]

theorem unpackNat_state (b d c : ℕ) :
    (unpackNat b d c).state = c / b ^ (2 * d) := by
  simp [unpackNat, Nat.div_div_eq_div_mul, show 2 * d = d * 2 by omega, pow_mul, sq]

theorem residue_periodic (b d : ℕ) :
    Function.Periodic (residue b d) (b ^ (2 * d + 1) : ℕ) := by
  intro j
  simp [residue]

theorem unpack_periodic (b d : ℕ) :
    Function.Periodic (unpack b d) (b ^ (2 * d + 1) : ℕ) := by
  intro j
  simp only [unpack, residue_periodic b d j]

theorem residue_lt {b d : ℕ} (hb : 2 ≤ b) (j : ℤ) :
    residue b d j < b ^ (2 * d + 1) := by
  have hp : (0 : ℤ) < (b ^ (2 * d + 1) : ℕ) := by
    exact_mod_cast pow_pos (by omega : 0 < b) (2 * d + 1)
  have hlo := Int.emod_nonneg j (ne_of_gt hp)
  have hhi := Int.emod_lt_of_pos j hp
  unfold residue
  omega

theorem unpack_pack {b d : ℕ} (hb : 2 ≤ b) (c : Code)
    (hl : c.left < b ^ d) (hr : c.right < b ^ d) (hs : c.state < b) :
    unpack b d (pack b d c : ℕ) = c := by
  have hp := pack_lt hb c hl hr hs
  have he : residue b d (pack b d c : ℕ) = pack b d c := by
    simp only [residue, ← Int.natCast_mod, Nat.mod_eq_of_lt hp, Int.toNat_natCast]
  rw [unpack, he, unpackNat_pack hb c hl hr]

theorem tail_bound {b d R : ℕ} (hb : 2 ≤ b) (hd : 0 < d) (hR : R < b ^ d) :
    R - R % b + b ≤ b ^ d := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  have hbpos : 0 < b := by omega
  have hdiv : R / b < b ^ e := by
    apply (Nat.div_lt_iff_lt_mul hbpos).2
    simpa only [pow_succ] using hR
  have hmod := Nat.div_add_mod R b
  have hle := Nat.mod_le R b
  have hsub : R - R % b = b * (R / b) := by omega
  rw [hsub, pow_succ]
  have hm := Nat.mul_le_mul_left b (Nat.succ_le_of_lt hdiv)
  nlinarith

def step (b : ℕ) (c : Code) (I : Instruction) : Code :=
  if I.move.val = 2 then
    ⟨I.writeSymbol + b * c.left, c.right / b, I.nextState⟩
  else if I.move.val = 0 then
    ⟨c.left / b, c.left % b + b * I.writeSymbol + b * (c.right - c.right % b),
      I.nextState⟩
  else
    ⟨c.left, c.right - c.right % b + I.writeSymbol, I.nextState⟩

theorem step_stacks_lt {b d : ℕ} (hb : 2 ≤ b) (hd : 0 < d)
    (c : Code) (I : Instruction) (hl : c.left < b ^ d) (hr : c.right < b ^ d)
    (hw : I.writeSymbol < b) :
    (step b c I).left < b ^ (d + 1) ∧ (step b c I).right < b ^ (d + 1) := by
  have hp : b ^ d ≤ b ^ (d + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have ht := tail_bound hb hd hr
  have htop : c.left % b < b := Nat.mod_lt _ (by omega)
  have hsq : b ^ (d + 1) = b ^ d * b := pow_succ _ _
  unfold step
  split_ifs
  · dsimp
    constructor
    · rw [hsq]
      have hm := Nat.mul_le_mul_left b (Nat.succ_le_of_lt hl)
      nlinarith
    · exact (Nat.div_le_self _ _).trans_lt (hr.trans_le hp)
  · dsimp
    constructor
    · exact (Nat.div_le_self _ _).trans_lt (hl.trans_le hp)
    · rw [hsq]
      have hm := Nat.mul_le_mul_left b ht
      have hw' := Nat.mul_le_mul_left b (Nat.succ_le_of_lt hw)
      nlinarith
  · dsimp
    constructor
    · exact hl.trans_le hp
    · have hstay : c.right - c.right % b + I.writeSymbol < b ^ d := by omega
      exact hstay.trans_le hp

@[simp] theorem step_state (b : ℕ) (c : Code) (I : Instruction) :
    (step b c I).state = I.nextState := by
  unfold step
  split_ifs <;> rfl

theorem step_pack_lt {b d : ℕ} (hb : 2 ≤ b) (hd : 0 < d)
    (c : Code) (I : Instruction) (hl : c.left < b ^ d) (hr : c.right < b ^ d)
    (hw : I.writeSymbol < b) (hs : I.nextState < b) :
    pack b (d + 2) (step b c I) < b ^ (2 * (d + 2) + 1) := by
  obtain ⟨hl', hr'⟩ := step_stacks_lt hb hd c I hl hr hw
  have hp : b ^ (d + 1) ≤ b ^ (d + 2) := Nat.pow_le_pow_right (by omega) (by omega)
  exact pack_lt hb _ (hl'.trans_le hp) (hr'.trans_le hp) (by simpa using hs)

end StackCode

namespace Detector

theorem isOpen : IsOpen detector := by
  have heq : detector = (fun q : Torus => q 0) ⁻¹'
      ((fun s : ℝ => (s : UnitAddCircle)) '' Set.Ioo (1 / 2 : ℝ) 1) := by
    ext q
    simp [detector, and_assoc]
  rw [heq]
  have hopen : IsOpen ((fun s : ℝ => (s : UnitAddCircle)) '' Set.Ioo (1 / 2 : ℝ) 1) :=
    QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  exact hopen.preimage (continuous_apply 0)

theorem mem_iff {x : Space} (hlo : 0 ≤ x 0) (hhi : x 0 < 1) :
    torusMk x ∈ detector ↔ 1 / 2 < x 0 := by
  constructor
  · rintro ⟨s, hslo, hshi, hs⟩
    have hx : x 0 ∈ Set.Ico (0 : ℝ) (0 + 1) := by
      simp only [zero_add, Set.mem_Ico]
      exact ⟨hlo, hhi⟩
    have hs' : s ∈ Set.Ico (0 : ℝ) (0 + 1) := by
      simp only [zero_add, Set.mem_Ico]
      exact ⟨by linarith, hshi⟩
    have h : s = x 0 := (AddCircle.coe_eq_coe_iff_of_mem_Ico hs' hx).1 hs
    simpa [h] using hslo
  · intro h
    exact ⟨x 0, h, hhi, rfl⟩

theorem initial_not_mem : torusMk initialParticle ∉ detector := by
  rw [mem_iff (by norm_num [initialParticle]) (by norm_num [initialParticle])]
  norm_num [initialParticle]

end Detector

end
end PeriodicLattice

end OAI
