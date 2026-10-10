import OAI.NumberTheory.Ostmann.Arithmetic.MovingKernelPair

namespace OAI

/-! # A uniform norm budget for the two-history giant kernel -/

namespace Ostmann
open scoped Classical ComplexConjugate SchwartzMap

theorem movingRealKernelPair_norm_variation {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hV : ∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V))
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (L R : ℝ) :
    ‖movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G L R‖ ≤
      (movingFourierVariationBudget ψ V lo hi n *
      (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 := by
  let W := pairedPolynomialFactors
    (movingSmoothPolynomialFactors value (T false) (movingCoordinateLeft false R)
      (movingCoordinateRight false R) ψ X lo hi hlo hhi φ G B D hB hD hφ hlip)
    (movingSmoothPolynomialFactors value (T true) (movingCoordinateLeft false R)
      (movingCoordinateRight false R) ψ X lo hi hlo hhi φ G B D hB hD hφ hlip)
  let g := movingRealGateWeight value (T false) (nodes false) X lo hi (movingRealPair false R L) *
    conj (movingRealGateWeight value (T true) (nodes true) X lo hi (movingRealPair false R L))
  have hg : ‖g‖ ≤ 1 := by
    dsimp only [g]
    rw [norm_mul, Complex.norm_conj]
    exact (mul_le_mul (movingRealGateWeight_norm value (T false) (nodes false) X lo hi _)
      (movingRealGateWeight_norm value (T true) (nodes true) X lo hi _) (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)
  have he := movingRealKernelPair_slice_polynomial value T nodes ψ X lo hi hlo hhi φ G
    B D hB hD hφ hlip hout false R L
  simp only [movingRealPair, Bool.false_eq_true, ite_false, topGiantReal, ite_true] at he
  have he' : movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G L R =
      g * smoothPolynomialWeight W L := he
  rw [he', norm_mul]
  calc
    _ ≤ 1 * smoothPolynomialBudget W :=
      mul_le_mul hg (smoothPolynomialWeight_norm W L) (norm_nonneg _) zero_le_one
    _ ≤ _ := by
      rw [one_mul]
      exact movingPairedSmoothPolynomialFactors_budget value T _ _ ψ X lo hi V hlo hhi hV
        φ G B D hB hD hφ hlip

end Ostmann

end OAI
