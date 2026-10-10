import OAI.NumberTheory.Ostmann.Arithmetic.RecursiveFrequencySupport

namespace OAI

/-! # The original Fourier weight retains its precise bottom cutoff -/

namespace Ostmann

open scoped Classical

/-- The original level-zero Fourier factor vanishes outside its prescribed
frequency range; each recursive coefficient retains every leaf cutoff. -/
theorem recursive_archimedean_square_with_leaf_cutoff {State : Type*}
    (sys : TransferHistorySystem State) (M : State → ℕ) (c : State → ℤ → ℝ)
    (cutoff : State → ℤ → ℤ → ℤ → ℝ) (X Δ C K : ℝ) (ψhat : ℝ → ℂ)
    (hc : ∀ σ v, |c σ v| ≤ 1) (hψ : ∀ u, ‖ψhat u‖ ≤ Real.exp K)
    (hwindow : ∀ σ v, c σ v ≠ 0 → 0 < M σ ∧ X * Real.exp (Δ - C) ≤ M σ)
    (hcut : ∀ σ s v w, |cutoff σ s v w| ≤ 1)
    (V : ℕ) (hfreq : ∀ σ v, c σ v ≠ 0 → v.natAbs ≤ V)
    (S : Finset ℤ) (n : ℕ) (σ : State) (t : FrequencyTree S n) :
    ‖recursiveTransferWeight sys
        (fun σ v => archimedeanLeafFactor X (M σ) v (c σ v) ψhat) cutoff n σ
        (frequencyTreeMap Subtype.val n t)‖ ^ 2 ≤
      Real.exp (-(2 ^ n : ℕ) * Δ + (2 ^ n : ℕ) * (C + 2 * K)) *
        frequencyLeafWeight (singleFrequencyLeaf S V) n t := by
  have hsize (τ : State) (v : ℤ) :
      ‖archimedeanLeafFactor X (M τ) v (c τ v) ψhat‖ ^ 2 ≤ Real.exp (-Δ + (C + 2 * K)) := by
    apply archimedeanLeafFactor_square_exp_le X (M τ) v (c τ v) Δ C K ψhat (hc τ v) hψ
    intro hv
    obtain ⟨hp, hb⟩ := hwindow τ v hv
    exact ⟨by exact_mod_cast hp, hb⟩
  have hleaf (τ : State) (v : ℤ)
      (hv : archimedeanLeafFactor X (M τ) v (c τ v) ψhat ≠ 0) : v.natAbs ≤ V := by
    apply hfreq τ v
    intro hc0
    apply hv
    simp only [archimedeanLeafFactor, hc0, mul_zero, Complex.ofReal_zero, zero_mul]
  have h := recursiveTransferWeight_square_with_leaf_cutoff sys _ cutoff
    (Real.exp (-Δ + (C + 2 * K))) (Real.exp_pos _).le hsize hcut V hleaf S n σ t
  apply h.trans_eq
  rw [← Real.exp_nat_mul]
  congr 2
  ring

end Ostmann

end OAI
