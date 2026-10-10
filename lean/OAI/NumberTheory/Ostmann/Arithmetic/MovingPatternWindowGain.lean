import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternKernelGain

namespace OAI

/-! # Uniform quartet gain for the actual moving Fourier windows -/

namespace Ostmann
open scoped SchwartzMap

/-- The tolerance is selected after the fixed Fourier profile and frequency
cost, and before the bulk length. All sharp cutoffs are included in `W`. -/
theorem exists_movingPatternKernelGain_window (ψ : 𝓢(ℝ, ℂ)) (n r₀ : ℕ)
    (A H B D F gain : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ lo hi : ℝ, lo ≤ hi →
      hi - lo ≤ Real.exp (H * m) → ∀ amp δ : ℝ,
      0 ≤ amp → amp ≤ Real.exp (F * m) → 0 ≤ δ →
      δ ≤ signedBulkGainTarget n (C + F) gain →
      let W := (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi n *
        (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
      (W * amp) * 4 ^ Fintype.card (TreeLeafIndex n × Fin m) * δ ^ m ≤
        Real.exp (-gain * m) := by
  obtain ⟨C, hC, hcost⟩ := movingPatternKernelBudget_exp_window ψ n r₀ A H B D hA hH
  refine ⟨2 * C, by positivity, ?_⟩
  intro m hm lo hi hhi hwidth amp δ hamp hampBound hδ hgain
  dsimp only
  let W := (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi n *
    (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
  have hW : 0 ≤ W := sq_nonneg _
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hWbound : W ≤ Real.exp (2 * C * m) := by
    apply (bulkKernelPair_smooth_le_budget ψ (Real.exp (A * m)) lo hi n
      (2 ^ n * (r₀ + m + 4 * n + 4)) (2 ^ n * (r₀ + m + 4 * n)) 0 B D).trans
    apply (hcost m lo hi hhi hwidth).trans
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hamp' : W * amp ≤ Real.exp ((2 * C + F) * m) := by
    apply (mul_le_mul hWbound hampBound hamp (Real.exp_nonneg _)).trans_eq
    rw [← Real.exp_add]
    congr 1
    ring
  have h := signedBulkGainTarget_bound n m (2 * C + F) gain 1 (W * amp) δ
    (by norm_num) (mul_nonneg hW hamp) hδ hamp' hgain
  simpa only [one_mul] using h

end Ostmann

end OAI
