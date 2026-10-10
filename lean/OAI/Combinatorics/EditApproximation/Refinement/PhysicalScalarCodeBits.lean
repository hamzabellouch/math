import OAI.Combinatorics.EditApproximation.Refinement.PhysicalScalarEncoding

namespace OAI

/-! Concrete coordinate pairing has constant-factor bit overhead. The
addresses are computed from coordinates, without enumerating a key space. -/

namespace EditApproximation

 theorem natPair_lt_two_pow {a b k : ℕ} (ha : a < 2 ^ k) (hb : b < 2 ^ k) :
    Nat.pair a b < 2 ^ (2 * k) := by
  calc
    _ < (max a b + 1) ^ 2 := Nat.pair_lt_max_add_one_sq a b
    _ ≤ (2 ^ k) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    _ = _ := by rw [← pow_mul]; congr 1; omega

 theorem natPair_lt_two_pow_scaled {a b k d : ℕ} (ha : a < 2 ^ k)
    (hb : b < 2 ^ (d * k)) (hd : 1 ≤ d) : Nat.pair a b < 2 ^ ((2 * d) * k) := by
  have hk : k ≤ d * k := by simpa only [one_mul] using Nat.mul_le_mul_right k hd
  have h := natPair_lt_two_pow (ha.trans_le (Nat.pow_le_pow_right (by decide) hk)) hb
  simpa only [Nat.mul_assoc] using h

 theorem physicalScalarCode_bound {M J N n exponent F Q R B : ℕ} (k : ℕ)
    (hnode : ∀ node : PhysicalNode M J, physicalNodeCode node < 2 ^ k)
    (hentry : ∀ entry : PhysicalEntry M J n, physicalEntryCode entry < 2 ^ k)
    (hscale : (dyadicScales N).length ≤ 2 ^ k)
    (hcell : n * 2 ^ exponent + 1 ≤ 2 ^ k)
    (hrange : B + 1 ≤ 2 ^ k) (htime : R ≤ 2 ^ k) (hM : M ≤ 2 ^ k)
    (hlabels : ∀ scale : Fin (dyadicScales N).length,
      (groupDyadicScales M ((dyadicScales N).get scale) F).length ≤ 2 ^ k)
    (key : PhysicalScalarKey M J N n exponent F Q R B) :
    physicalScalarCode key < 2 ^ (64 * k + 1) := by
  rcases key with ⟨key, index⟩
  cases key with
  | inl online =>
    have h0 := natPair_lt_two_pow (online.2.val.isLt.trans_le hrange) (index.isLt.trans_le htime)
    have h1 := natPair_lt_two_pow_scaled (online.1.2.1.isLt.trans_le hscale) h0 (by decide : 1 ≤ 2)
    have h2 := natPair_lt_two_pow_scaled (hentry (online.1.1.val, online.1.2.2)) h1 (by decide : 1 ≤ 4)
    have h2' : Nat.pair (physicalEntryCode (online.1.1.val, online.1.2.2))
        (Nat.pair online.1.2.1.val (Nat.pair online.2.val.val index.val)) < 2 ^ (64 * k) :=
      h2.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
    change 2 * _ < _
    rw [pow_succ]
    omega
  | inr group =>
    have h0 := natPair_lt_two_pow
      (index.2.1.isLt.trans_le (hlabels group.2.1))
      (index.2.2.isLt.trans_le ((min_le_left _ _).trans hM))
    have h1 := natPair_lt_two_pow_scaled (index.1.isLt.trans_le htime) h0 (by decide : 1 ≤ 2)
    have h2 := natPair_lt_two_pow_scaled (group.2.2.2.isLt.trans_le hcell) h1 (by decide : 1 ≤ 4)
    have h3 := natPair_lt_two_pow_scaled (group.2.2.1.isLt.trans_le hcell) h2 (by decide : 1 ≤ 8)
    have h4 := natPair_lt_two_pow_scaled (group.2.1.isLt.trans_le hscale) h3 (by decide : 1 ≤ 16)
    have h5 := natPair_lt_two_pow_scaled (hnode group.1.val) h4 (by decide : 1 ≤ 32)
    norm_num only at h5
    change 2 * _ + 1 < _
    rw [pow_succ]
    omega

end EditApproximation

end OAI
