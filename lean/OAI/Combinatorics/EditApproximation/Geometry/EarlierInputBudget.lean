import OAI.Combinatorics.EditApproximation.Queries.QueryEarlierInputs
import OAI.Combinatorics.EditApproximation.Refinement.ComputedCurrentQueryBudget

namespace OAI

/-! The explicit wide-history cover fits the polynomial earlier-input
budget used in the dependency-path count. -/

namespace EditApproximation

def localEarlierBudget (window cells M P F history : ℕ) : ℕ :=
  window * ((64 * F * P + 2) ^ 2 + cells * (P + 1) ^ 2 + 1) *
    M * history * (40 * P + 2) ^ 2

theorem queryEarlierInputCover_le_budget {nx ny M : ℕ} (parent : TargetInterval nx)
    (N P F exponent history window cells : ℕ) (a : ℚ)
    (initial : TargetInterval ny → ℚ) (q : TargetInterval ny)
    (hP : ∃ e : ℕ, P = 2 ^ e) (hF : 1 ≤ F) (hw : 0 ≤ initial q)
    (hwindow : (dyadicQueryWindow N (initial q) a F).length ≤ window)
    (hcells : ((32 * F + 2) * 2 ^ exponent + 2) ^ 2 ≤ cells) :
    (queryEarlierInputCover (M := M) parent N P F exponent history a initial q).card ≤
      localEarlierBudget window cells M P F history := by
  have hmembers : (64 * F * P + 2) ^ 2 +
      ((32 * F + 2) * 2 ^ exponent + 2) ^ 2 * (P + 1) ^ 2 + 1 ≤
      (64 * F * P + 2) ^ 2 + cells * (P + 1) ^ 2 + 1 :=
    Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_right _ hcells) _) _
  exact (queryEarlierInputCover_card parent N P F exponent history a initial q hP hF hw).trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right history
      (Nat.mul_le_mul_right M (Nat.mul_le_mul hwindow hmembers))))

theorem localEarlierBudget_poly (H p window cells M P F history : ℕ)
    (hH : 64 ≤ H) (hPpos : 1 ≤ P) (hP : P ≤ H ^ (p + 20))
    (hwindow : window ≤ H ^ 3) (hcells : cells ≤ H ^ 84)
    (hM : M ≤ H) (hF : F ≤ H) (hhistory : history ≤ H ^ 2) :
    localEarlierBudget window cells M P F history ≤ H ^ (256 * (p + 1)) := by
  have hHone : 1 ≤ H := by omega
  have h64 : 64 * F ≤ H ^ 2 := by
    calc
      _ ≤ H * H := Nat.mul_le_mul hH hF
      _ = H ^ 2 := by ring
  have hfirstBase : 64 * F * P + 2 ≤ H ^ 3 * P := by
    have hm := Nat.mul_le_mul_right P h64
    have hp : 2 ≤ H ^ 2 * P := by
      have hlarge : 2 ≤ H ^ 2 := (by norm_num : 2 ≤ (64 : ℕ) ^ 2).trans
        (Nat.pow_le_pow_left hH 2)
      exact hlarge.trans (Nat.le_mul_of_pos_right _ hPpos)
    have hh : 2 * H ^ 2 ≤ H ^ 3 := by
      calc
        _ ≤ H * H ^ 2 := Nat.mul_le_mul_right _ (by omega : 2 ≤ H)
        _ = H ^ 3 := by ring
    nlinarith only [hm, hp, Nat.mul_le_mul_right P hh]
  have hfirst : (64 * F * P + 2) ^ 2 ≤ H ^ 86 * P ^ 2 := by
    calc
      _ ≤ (H ^ 3 * P) ^ 2 := Nat.pow_le_pow_left hfirstBase 2
      _ = H ^ 6 * P ^ 2 := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (pow_le_pow_right₀ hHone (by omega : 6 ≤ 86))
  have hPadd : P + 1 ≤ H * P := by nlinarith
  have hsecond : cells * (P + 1) ^ 2 ≤ H ^ 86 * P ^ 2 := by
    calc
      _ ≤ H ^ 84 * (H * P) ^ 2 := Nat.mul_le_mul hcells (Nat.pow_le_pow_left hPadd 2)
      _ = _ := by ring
  have hone : 1 ≤ H ^ 86 * P ^ 2 := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul (one_le_pow₀ hHone (n := 86)) (one_le_pow₀ hPpos (n := 2))
  have hsum : (64 * F * P + 2) ^ 2 + cells * (P + 1) ^ 2 + 1 ≤ H ^ 88 * P ^ 2 := by
    have hh : 3 * H ^ 86 ≤ H ^ 88 := by
      calc
        _ ≤ H ^ 2 * H ^ 86 := Nat.mul_le_mul_right _
          ((by norm_num : 3 ≤ (64 : ℕ) ^ 2).trans (Nat.pow_le_pow_left hH 2))
        _ = _ := by ring
    nlinarith only [hfirst, hsecond, hone, Nat.mul_le_mul_right (P ^ 2) hh]
  have hwideBase : 40 * P + 2 ≤ H ^ 2 * P := by
    have hh : 42 ≤ H ^ 2 := (by norm_num : 42 ≤ (64 : ℕ) ^ 2).trans
      (Nat.pow_le_pow_left hH 2)
    nlinarith only [Nat.mul_le_mul_right P hh, hPpos]
  have hwide : (40 * P + 2) ^ 2 ≤ H ^ 4 * P ^ 2 := by
    calc
      _ ≤ (H ^ 2 * P) ^ 2 := Nat.pow_le_pow_left hwideBase 2
      _ = _ := by ring
  calc
    localEarlierBudget window cells M P F history ≤
        H ^ 3 * (H ^ 88 * P ^ 2) * H * H ^ 2 * (H ^ 4 * P ^ 2) := by
      exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul
        (Nat.mul_le_mul hwindow hsum) hM) hhistory) hwide
    _ = H ^ 98 * P ^ 4 := by ring
    _ ≤ H ^ 98 * (H ^ (p + 20)) ^ 4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hP 4)
    _ = H ^ (98 + (p + 20) * 4) := by rw [← pow_mul, ← pow_add]
    _ ≤ H ^ (256 * (p + 1)) := pow_le_pow_right₀ hHone (by omega)

end EditApproximation

end OAI
