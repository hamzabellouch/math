import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousComplexFiniteRank

namespace OAI

/-! # Complex finite-rank decomposition from the actual weak-null estimate

Choosing a sufficiently small real remainder absorbs the norm factor in
complexification. The only input is the quantitative weak-null estimate
already proved for the actual linearized propagator.
-/

open Filter Topology

namespace DefocusingNLS

theorem homogeneousOperator_complexFiniteRank_contraction (a k r : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (hr : 0 ≤ r) (hr1 : r < 1 / 4)
    (T : HomogeneousY a k →L[ℝ] HomogeneousY a k)
    (hweak : ∀ u : ℕ → HomogeneousY a k, (∀ j, ‖u j‖ ≤ 1) →
      (∀ ℓ : HomogeneousY a k →L[ℝ] ℂ,
        Tendsto (fun j => ℓ (u j)) atTop (𝓝 0)) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ‖T (u j)‖ ^ 2 < r + ε) :
    ∃ B K : (HomogeneousY a k × HomogeneousY a k) →L[ℂ]
        (HomogeneousY a k × HomogeneousY a k),
      homogeneousComplexification a k ha ha1 hk T = B + K ∧
      ‖B‖ < 1 ∧ FiniteDimensional ℂ (LinearMap.range K.toLinearMap) := by
  obtain ⟨B, K, hT, hB, hK⟩ := homogeneousOperator_finiteRank_bound a k r (1 / 2)
    ha1 hk hr (by norm_num) (by norm_num at *; exact hr1) T hweak
  refine ⟨homogeneousComplexification a k ha ha1 hk B,
    homogeneousComplexification a k ha ha1 hk K, ?_, ?_, ?_⟩
  · rw [hT, homogeneousComplexification_add]
  · have h := homogeneousComplexification_norm_le a k ha ha1 hk B
    linarith
  · exact homogeneousComplexification_finiteRank a k ha ha1 hk K hK

end DefocusingNLS

end OAI
