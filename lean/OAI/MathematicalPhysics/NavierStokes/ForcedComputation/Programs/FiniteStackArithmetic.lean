import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.LatticeStacks

namespace OAI

/-! Faithfulness of finite little-endian integer stacks, including their
infinite zero tails. This is used for the entire finite recorder table. -/

namespace ForcedComputation.Lattice

theorem stackValue_injective_prefix {b d : ℕ} (hb : 0 < b)
    {a c : ℕ → ℕ} (ha : ∀ i < d, a i < b) (hc : ∀ i < d, c i < b)
    (he : stackValue b d a = stackValue b d c) : ∀ i < d, a i = c i := by
  induction d generalizing a c with
  | zero => intro i hi; omega
  | succ d ih =>
    have hhead : a 0 = c 0 := by
      have h := congrArg (fun n => n % b) he
      simpa only [stackValue_head (ha 0 (by omega)), stackValue_head (hc 0 (by omega))] using h
    have htail : stackValue b d (fun i => a (i + 1)) =
        stackValue b d (fun i => c (i + 1)) := by
      have h := congrArg (fun n => n / b) he
      simpa only [stackValue_tail hb (ha 0 (by omega)),
        stackValue_tail hb (hc 0 (by omega))] using h
    intro i hi
    cases i with
    | zero => exact hhead
    | succ i =>
      exact ih (fun j hj => ha (j + 1) (by omega))
        (fun j hj => hc (j + 1) (by omega)) htail i (by omega)

theorem stackValue_injective_zero_tail {b d : ℕ} (hb : 0 < b)
    {a c : ℕ → ℕ} (ha : ∀ i, a i < b) (hc : ∀ i, c i < b)
    (ha0 : ∀ i, d ≤ i → a i = 0) (hc0 : ∀ i, d ≤ i → c i = 0)
    (he : stackValue b d a = stackValue b d c) : a = c := by
  funext i
  by_cases hi : i < d
  · exact stackValue_injective_prefix hb (fun j _ => ha j) (fun j _ => hc j) he i hi
  · rw [ha0 i (by omega), hc0 i (by omega)]

theorem prepend_injective {b a c L R : ℕ} (hb : 0 < b) (ha : a < b) (hc : c < b)
    (he : a + b * L = c + b * R) : a = c ∧ L = R := by
  have hm := congrArg (fun n => n % b) he
  have hd := congrArg (fun n => n / b) he
  constructor
  · simpa only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt hc] using hm
  · simpa only [Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt ha,
      Nat.div_eq_of_lt hc, Nat.zero_add] using hd

theorem nat_eq_of_mod_div_eq {b L R : ℕ} (hm : L % b = R % b) (hd : L / b = R / b) :
    L = R := by
  calc
    L = L % b + b * (L / b) := (Nat.mod_add_div L b).symm
    _ = R % b + b * (R / b) := by rw [hm, hd]
    _ = R := Nat.mod_add_div R b

/-- The written digit and both old stack tails are recoverable from the
new stacks, once the incoming movement is known. -/
theorem nextStacks_recover {b L₁ L₂ R₁ R₂ a₁ a₂ : ℕ}
    (hb : 0 < b) (ha₁ : a₁ < b) (ha₂ : a₂ < b) (m : Fin 3)
    (hL : nextLeft b L₁ a₁ m = nextLeft b L₂ a₂ m)
    (hR : nextRight b L₁ R₁ a₁ m = nextRight b L₂ R₂ a₂ m) :
    L₁ = L₂ ∧ R₁ / b = R₂ / b ∧ a₁ = a₂ := by
  fin_cases m
  · simp only [nextLeft, nextRight] at hL hR
    obtain ⟨hm, ht⟩ := prepend_injective hb (Nat.mod_lt _ hb) (Nat.mod_lt _ hb) hR
    obtain ⟨ha, hq⟩ := prepend_injective hb ha₁ ha₂ ht
    exact ⟨nat_eq_of_mod_div_eq hm hL, hq, ha⟩
  · simp only [nextLeft, nextRight] at hL hR
    obtain ⟨ha, hq⟩ := prepend_injective hb ha₁ ha₂ hR
    exact ⟨hL, hq, ha⟩
  · simp only [nextLeft, nextRight] at hL hR
    obtain ⟨ha, hq⟩ := prepend_injective hb ha₁ ha₂ hL
    exact ⟨hq, hR, ha⟩

theorem nextStacks_injective_of_read {b L₁ L₂ R₁ R₂ a₁ a₂ : ℕ}
    (hb : 0 < b) (ha₁ : a₁ < b) (ha₂ : a₂ < b) (m : Fin 3)
    (hL : nextLeft b L₁ a₁ m = nextLeft b L₂ a₂ m)
    (hR : nextRight b L₁ R₁ a₁ m = nextRight b L₂ R₂ a₂ m)
    (hread : R₁ % b = R₂ % b) : L₁ = L₂ ∧ R₁ = R₂ ∧ a₁ = a₂ := by
  obtain ⟨hl, hr, ha⟩ := nextStacks_recover hb ha₁ ha₂ m hL hR
  exact ⟨hl, nat_eq_of_mod_div_eq hread hr, ha⟩

end ForcedComputation.Lattice

end OAI
