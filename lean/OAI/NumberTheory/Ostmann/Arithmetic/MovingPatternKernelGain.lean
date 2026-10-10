import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternKernelCost
import OAI.NumberTheory.Ostmann.Construction.SignedBulkGain

namespace OAI

/-! # The quartet gain absorbs the actual sharp-kernel main term -/

namespace Ostmann
open scoped SchwartzMap

theorem bulkKernelPair_smooth_le_budget (ψ : 𝓢(ℝ, ℂ)) (V lo hi : ℝ)
    (n d r e : ℕ) (B D : ℝ) :
    (movingFourierVariationBudget ψ V lo hi n *
      (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 ≤
    bulkKernelPairComparisonBudget ψ V lo hi n d r e B D := by
  let c := 2 * (((2 ^ n + (2 ^ n - 1)) * (2 * (n * d + e) + r)) +
    ((3 * (2 ^ n - 1) + 2 * 2 ^ n) * (2 * (n * d + e) + r)))
  have hc : (1 : ℝ) ≤ ((c + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 c
  exact le_mul_of_one_le_left (sq_nonneg _) hc

/-- The tolerance is selected after the fixed Fourier profile and frequency
cost, and before the bulk length. All sharp cutoffs are included in `W`. -/
theorem exists_movingPatternKernelGain (ψ : 𝓢(ℝ, ℂ)) (n r₀ : ℕ)
    (A lo hi B D F gain : ℝ) (hA : 0 ≤ A) (hhi : lo ≤ hi) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ amp δ : ℝ,
      0 ≤ amp → amp ≤ Real.exp (F * m) → 0 ≤ δ →
      δ ≤ signedBulkGainTarget n (C + F) gain →
      let W := (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi n *
        (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
      (W * amp) * 4 ^ Fintype.card (TreeLeafIndex n × Fin m) * δ ^ m ≤
        Real.exp (-gain * m) := by
  obtain ⟨C, hC, hcost⟩ := movingPatternKernelBudget_exp ψ n r₀ A lo hi B D hA hhi
  refine ⟨2 * C, by positivity, ?_⟩
  intro m hm amp δ hamp hampBound hδ hgain
  dsimp only
  let W := (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi n *
    (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
  have hW : 0 ≤ W := sq_nonneg _
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hWbound : W ≤ Real.exp (2 * C * m) := by
    apply (bulkKernelPair_smooth_le_budget ψ (Real.exp (A * m)) lo hi n
      (2 ^ n * (r₀ + m + 4 * n + 4)) (2 ^ n * (r₀ + m + 4 * n)) 0 B D).trans
    apply (hcost m).trans
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
