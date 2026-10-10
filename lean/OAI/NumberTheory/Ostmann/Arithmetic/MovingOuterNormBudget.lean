import OAI.NumberTheory.Ostmann.Arithmetic.MovingOuterJointComparison

namespace OAI

/-! # A uniform norm budget for the full giant kernel -/

namespace Ostmann
open scoped Classical ComplexConjugate SchwartzMap

theorem movingOuterKernel_norm_variation {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hV : ∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V))
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool) (L R : ℝ) :
    ‖movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal L R‖ ≤
      giantOuterScalar diagonal * movingOuterVariationBudget ψ V lo hi n B D diagonal := by
  have hs : 0 ≤ giantOuterScalar diagonal := by cases diagonal <;> simp [giantOuterScalar, (Real.exp_pos _).le]
  let W := movingOuterPolynomialFactors value T (movingCoordinateLeft false R) (movingCoordinateRight false R)
    ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip diagonal
  let g := movingRealGateWeight value (T false) (nodes false) X lo hi (movingRealPair false R L) *
    conj (movingRealGateWeight value (T true) (nodes true) X lo hi (movingRealPair false R L))
  have hg : ‖g‖ ≤ 1 := by
    dsimp only [g]
    rw [norm_mul, Complex.norm_conj]
    exact (mul_le_mul (movingRealGateWeight_norm value (T false) (nodes false) X lo hi _)
      (movingRealGateWeight_norm value (T true) (nodes true) X lo hi _) (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)
  have he := movingOuterKernel_slice_polynomial value T nodes ψ X lo hi hlo hhi φ G
    Jleft Jright B D hB hD hφ hlip hout diagonal false R L
  simp only [movingRealPair, Bool.false_eq_true, ite_false, topGiantReal, ite_true] at he
  have he' : movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal L R =
      ((giantOuterScalar diagonal : ℂ) * g) * smoothPolynomialWeight W L := he
  rw [he', norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs]
  calc
    _ ≤ (giantOuterScalar diagonal * 1) * smoothPolynomialBudget W :=
      mul_le_mul (mul_le_mul_of_nonneg_left hg hs) (smoothPolynomialWeight_norm W L)
        (norm_nonneg _) (by positivity)
    _ ≤ _ := by
      rw [mul_one]
      exact mul_le_mul_of_nonneg_left
        (movingOuterPolynomialFactors_budget value T _ _ ψ X lo hi V hlo hhi hV φ G Jleft Jright B D hB hD hφ hlip diagonal) hs

end Ostmann

end OAI
