import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingCompactCommutator
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingCompactLowProduct
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingCommutatorCoefficient
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ApproximateNullLimit

namespace OAI

/-! # Compact action for coefficients approximated by fixed compact profiles -/

open Filter Topology
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

/-- Uniform eventual approximation in the actual expanding norm by sampled compact functions. -/
def ExpandingCompactApproximation (a k : ℝ) (ha1 : a < 1) (hk : 8 < k)
    (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n) (q : ℕ → FourierL2) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ (R : ℝ) (K : 𝓢(E, ℂ)),
    (∀ y : E, R < ‖y‖ → K y = 0) ∧ ∀ᶠ n in atTop,
      ‖q n - schwartzTorusSample a k (L n) ha1 hk (hL n) (radianFourierKernel K)‖ < δ

theorem tendsto_expandingApproximate_commutator (a M : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hN : 8 < ((N + 1 : ℕ) : ℝ))
    (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n) (hLinf : Tendsto L atTop atTop)
    (q : ℕ → FourierL2) (hq : ExpandingCompactApproximation a (N + 1 : ℕ) ha1 hN L hL q)
    (f : ℕ → FourierL2) (hf : ∀ n, ‖f n‖ ≤ M)
    (hlocal : ∀ R ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ y : E, ‖y‖ ≤ R →
      ‖expandingTorusFunction a (N + 1 : ℕ) (L n) (f n)
        (euclideanToTorus ((L n)⁻¹ • y))‖ < ε)
    (j : Fin (N + 1) → Fin 12) :
    Tendsto (fun n => expandingProductCommutator a (L n) (N + 1) ha ha1 hN (hL n) j (q n) (f n))
      atTop (𝓝 0) := by
  let C : ℝ := (2 * Real.sqrt (4 ^ ((N + 1 : ℕ) : ℝ)) + 1) * expandingEmbeddingBound a (N + 1 : ℕ)
  have hC : 0 ≤ C := by dsimp [C]; unfold expandingEmbeddingBound; positivity
  have hM : 0 ≤ M := (norm_nonneg (f 0)).trans (hf 0)
  apply tendsto_zero_of_null_approximations
  intro ε hε
  let δ := ε / (C * M + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨R, K, hK, herr⟩ := hq δ hδ
  refine ⟨fun n => expandingProductCommutator a (L n) (N + 1) ha ha1 hN (hL n) j
    (schwartzTorusSample a (N + 1 : ℕ) (L n) ha1 hN (hL n) (radianFourierKernel K)) (f n),
    tendsto_expandingSample_commutator a M R N ha ha1 hN L hL hLinf f hf hlocal K hK j, ?_⟩
  have hδbound : C * δ * M ≤ ε := by
    have he : δ * (C * M + 1) = ε := div_mul_cancel₀ _ (by positivity)
    nlinarith [hδ.le]
  filter_upwards [herr] with n hn
  exact (expandingProductCommutator_coefficient_difference a (L n) (N + 1) ha ha1 hN (hL n)
    j (q n) _ (f n)).trans ((mul_le_mul
      (mul_le_mul_of_nonneg_left hn.le hC) (hf n) (norm_nonneg _)
      (mul_nonneg hC hδ.le)).trans hδbound)

theorem tendsto_expandingApproximate_lowEnergy_product (a M : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hN : 8 < (N : ℝ))
    (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n) (hLinf : Tendsto L atTop atTop)
    (q : ℕ → FourierL2) (hq : ExpandingCompactApproximation a N ha1 hN L hL q)
    (f : ℕ → FourierL2) (hf : ∀ n, ‖f n‖ ≤ M)
    (hlocal : ∀ R ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ y : E, ‖y‖ ≤ R →
      ‖expandingTorusFunction a N (L n) (f n) (euclideanToTorus ((L n)⁻¹ • y))‖ < ε) :
    Tendsto (fun n => expandingLowEnergy a N (L n) (hL n)
      (expandingProduct a N (L n) ha ha1 hN (hL n) (q n) (f n))) atTop (𝓝 0) := by
  let C : ℝ := 2 * Real.sqrt (4 ^ (N : ℝ)) * expandingEmbeddingBound a N
  have hC : 0 ≤ C := by dsimp [C]; unfold expandingEmbeddingBound; positivity
  have hM : 0 ≤ M := (norm_nonneg (f 0)).trans (hf 0)
  apply tendsto_zero_of_null_approximations
  intro ε hε
  let δ := ε / (C * M + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨R, K, hK, herr⟩ := hq δ hδ
  let r := fun n => schwartzTorusSample a N (L n) ha1 hN (hL n) (radianFourierKernel K)
  refine ⟨fun n => expandingLowEnergy a N (L n) (hL n)
    (expandingProduct a N (L n) ha ha1 hN (hL n) (r n) (f n)),
    tendsto_expandingSample_lowEnergy_product a M R N ha ha1 hN L hL hLinf f hf hlocal K hK, ?_⟩
  have hδbound : C * δ * M ≤ ε := by
    have he : δ * (C * M + 1) = ε := div_mul_cancel₀ _ (by positivity)
    nlinarith [hδ.le]
  filter_upwards [herr] with n hn
  have he : expandingProduct a N (L n) ha ha1 hN (hL n) (q n) (f n) -
      expandingProduct a N (L n) ha ha1 hN (hL n) (r n) (f n) =
      expandingProduct a N (L n) ha ha1 hN (hL n) (q n - r n) (f n) := by
    exact (congrArg (fun B : FourierL2 →L[ℂ] FourierL2 => B (f n))
      ((expandingBilinearProduct a N (L n) ha ha1 hN (hL n)).map_sub (q n) (r n))).symm
  rw [← map_sub, he]
  exact (expandingLowEnergy_norm_le a N (L n) (hL n) _).trans
    ((expandingProduct_norm_le a N (L n) ha ha1 hN (hL n) _ _).trans
      ((mul_le_mul (mul_le_mul_of_nonneg_left hn.le hC) (hf n) (norm_nonneg _)
        (mul_nonneg hC hδ.le)).trans hδbound))

end DefocusingNLS

end OAI
