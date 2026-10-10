import OAI.NumberTheory.Ostmann.Construction.TransferHistoryEnergy
import OAI.NumberTheory.Ostmann.Construction.TransferredPivotSubstitution
import OAI.NumberTheory.Ostmann.Construction.HistorySmoothBound

namespace OAI

/-! # The recursive weight with its actual reconstructed integer pivots -/

namespace Ostmann

open scoped BigOperators Classical

def historyPivot {State : Type*} (sys : TransferHistorySystem State)
    (σ : State) (s v w : ℤ) : ℕ :=
  reconstructedPivot (v * sys.rightProduct σ - w * sys.leftProduct σ) s

theorem ValidTransferNode.historyPivot_eq {State : Type*} {sys : TransferHistorySystem State}
    {σ : State} {s v w : ℤ} {P : ℕ} (h : ValidTransferNode sys σ s v w P) :
    historyPivot sys σ s v w = P :=
  reconstructedPivot_of_eq _ _ h.root_ne_zero P h.relation

/-- The node indicator contains precisely the arithmetic support used for
history rigidity. Other original range/bin cutoffs are carried by `cutoff`. -/
noncomputable def recursiveTransferWeight {State : Type*} (sys : TransferHistorySystem State)
    (leaf : State → ℤ → ℂ) (cutoff : State → ℤ → ℤ → ℤ → ℝ) :
    (n : ℕ) → State → FrequencyTree ℤ n → ℂ
  | 0, σ, v => leaf σ v
  | n + 1, σ, t =>
      let v := frequencyRoot n t.2.1
      let w := frequencyRoot n t.2.2
      let P := historyPivot sys σ t.1 v w
      if ValidTransferNode sys σ t.1 v w P then
        (cutoff σ t.1 v w : ℂ) *
          recursiveTransferWeight sys leaf cutoff n (sys.leftState σ P) t.2.1 *
          star (recursiveTransferWeight sys leaf cutoff n (sys.rightState σ P) t.2.2)
      else 0

/-- No witness choices enter the recursive weight: the integer equation
forces the pivot at every valid node. -/
theorem recursiveTransferWeight_node {State : Type*} (sys : TransferHistorySystem State)
    (leaf : State → ℤ → ℂ) (cutoff : State → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ (n + 1)) (P : ℕ)
    (hP : ValidTransferNode sys σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P) :
    recursiveTransferWeight sys leaf cutoff (n + 1) σ t =
      (cutoff σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) : ℂ) *
        recursiveTransferWeight sys leaf cutoff n (sys.leftState σ P) t.2.1 *
        star (recursiveTransferWeight sys leaf cutoff n (sys.rightState σ P) t.2.2) := by
  simp only [recursiveTransferWeight, hP.historyPivot_eq, hP, ite_true]

theorem recursiveTransferWeight_nonzero_valid {State : Type*} (sys : TransferHistorySystem State)
    (leaf : State → ℤ → ℂ) (cutoff : State → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ n)
    (ht : recursiveTransferWeight sys leaf cutoff n σ t ≠ 0) :
    ValidTransferHistory sys n σ t := by
  induction n generalizing σ with
  | zero => trivial
  | succ n ih =>
    let P := historyPivot sys σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
    by_cases hP : ValidTransferNode sys σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P
    · rw [recursiveTransferWeight_node sys leaf cutoff n σ t P hP] at ht
      have hl : recursiveTransferWeight sys leaf cutoff n (sys.leftState σ P) t.2.1 ≠ 0 := by
        intro hz
        simp only [hz, mul_zero, zero_mul, ne_eq, not_true_eq_false] at ht
      have hr : recursiveTransferWeight sys leaf cutoff n (sys.rightState σ P) t.2.2 ≠ 0 := by
        intro hz
        simp only [hz, star_zero, mul_zero, ne_eq, not_true_eq_false] at ht
      exact ⟨P, hP, ih _ _ hl, ih _ _ hr⟩
    · exact False.elim (ht (by simp only [recursiveTransferWeight, P, hP, ite_false]))

/-- Each squaring doubles the number of bottom weights and never adds an
absolute-value loss for a cutoff or an invalid arithmetic node. -/
theorem recursiveTransferWeight_square_le {State : Type*} (sys : TransferHistorySystem State)
    (leaf : State → ℤ → ℂ) (cutoff : State → ℤ → ℤ → ℤ → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hleaf : ∀ σ v, ‖leaf σ v‖ ^ 2 ≤ B)
    (hcut : ∀ σ s v w, |cutoff σ s v w| ≤ 1)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ n) :
    ‖recursiveTransferWeight sys leaf cutoff n σ t‖ ^ 2 ≤ B ^ (2 ^ n) := by
  induction n generalizing σ with
  | zero => simpa only [recursiveTransferWeight, pow_zero, pow_one] using hleaf σ t
  | succ n ih =>
    let P := historyPivot sys σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
    by_cases hP : ValidTransferNode sys σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P
    · rw [recursiveTransferWeight_node sys leaf cutoff n σ t P hP,
        norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs, mul_pow, mul_pow]
      have hc : |cutoff σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)| ^ 2 ≤ 1 := by
        simpa using pow_le_pow_left₀ (abs_nonneg _) (hcut σ t.1 _ _) 2
      calc
        _ ≤ (1 * B ^ (2 ^ n)) * B ^ (2 ^ n) :=
          mul_le_mul (mul_le_mul hc (ih _ _) (sq_nonneg _) (by norm_num))
            (ih _ _) (sq_nonneg _) (by positivity)
        _ = _ := by rw [one_mul, ← pow_add, pow_succ]; congr 1; omega
    · simp only [recursiveTransferWeight, P, hP, ite_false, norm_zero, zero_pow (by decide : 2 ≠ 0)]
      positivity

/-- The manuscript's level-zero modulus window gives the full history
square bound, with exactly `2^n` copies of its exponent. -/
theorem recursiveTransferWeight_square_exp_le {State : Type*} (sys : TransferHistorySystem State)
    (leaf : State → ℤ → ℂ) (cutoff : State → ℤ → ℤ → ℤ → ℝ)
    (Δ K : ℝ) (hleaf : ∀ σ v, ‖leaf σ v‖ ^ 2 ≤ Real.exp (-Δ + K))
    (hcut : ∀ σ s v w, |cutoff σ s v w| ≤ 1)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ n) :
    ‖recursiveTransferWeight sys leaf cutoff n σ t‖ ^ 2 ≤
      Real.exp (-(2 ^ n : ℕ) * Δ + (2 ^ n : ℕ) * K) := by
  apply (recursiveTransferWeight_square_le sys leaf cutoff _ (Real.exp_pos _).le hleaf hcut n σ t).trans_eq
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- The leaf estimate is derived from the product window on every nonzero
cutoff, including its boundary. It is not a new norm hypothesis. -/
theorem archimedeanLeafFactor_square_exp_le (X M s c Δ C K : ℝ)
    (ψhat : ℝ → ℂ) (hc : |c| ≤ 1)
    (hψ : ∀ u, ‖ψhat u‖ ≤ Real.exp K)
    (hwindow : c ≠ 0 → 0 < M ∧ X * Real.exp (Δ - C) ≤ M) :
    ‖archimedeanLeafFactor X M s c ψhat‖ ^ 2 ≤ Real.exp (-Δ + (C + 2 * K)) := by
  by_cases hc0 : c = 0
  · simp only [archimedeanLeafFactor, hc0, mul_zero, Complex.ofReal_zero,
      zero_mul, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    exact (Real.exp_pos _).le
  · obtain ⟨hM, hMX⟩ := hwindow hc0
    have hratio : Real.sqrt (X / M) * Real.exp K ≤ Real.exp (K + (C - Δ) / 2) := by
      calc
        _ ≤ Real.exp ((C - Δ) / 2) * Real.exp K :=
          mul_le_mul_of_nonneg_right (sqrt_ratio_le_exp X M Δ C hM hMX) (Real.exp_pos _).le
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    have hb := archimedeanLeafFactor_norm_le X M s c (Real.exp K)
      (Real.exp (K + (C - Δ) / 2)) ψhat hc hψ (Real.exp_pos _).le hratio
    apply (pow_le_pow_left₀ (norm_nonneg _) hb 2).trans_eq
    rw [← Real.exp_nat_mul]
    congr 1
    ring

/-- The recursively substituted coefficient inherits its square bound
from the actual initial product ranges and Fourier bound. -/
theorem recursive_archimedean_square_exp_le {State : Type*}
    (sys : TransferHistorySystem State) (M : State → ℕ) (c : State → ℤ → ℝ)
    (cutoff : State → ℤ → ℤ → ℤ → ℝ) (X Δ C K : ℝ) (ψhat : ℝ → ℂ)
    (hc : ∀ σ v, |c σ v| ≤ 1) (hψ : ∀ u, ‖ψhat u‖ ≤ Real.exp K)
    (hwindow : ∀ σ v, c σ v ≠ 0 → 0 < M σ ∧ X * Real.exp (Δ - C) ≤ M σ)
    (hcut : ∀ σ s v w, |cutoff σ s v w| ≤ 1)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ n) :
    ‖recursiveTransferWeight sys
      (fun σ v => archimedeanLeafFactor X (M σ) v (c σ v) ψhat) cutoff n σ t‖ ^ 2 ≤
      Real.exp (-(2 ^ n : ℕ) * Δ + (2 ^ n : ℕ) * (C + 2 * K)) := by
  apply recursiveTransferWeight_square_exp_le sys _ cutoff Δ (C + 2 * K) _ hcut n σ t
  intro τ v
  apply archimedeanLeafFactor_square_exp_le X (M τ) v (c τ v) Δ C K ψhat (hc τ v) hψ
  intro hn
  obtain ⟨hp, hb⟩ := hwindow τ v hn
  exact ⟨by exact_mod_cast hp, hb⟩

end Ostmann

end OAI
