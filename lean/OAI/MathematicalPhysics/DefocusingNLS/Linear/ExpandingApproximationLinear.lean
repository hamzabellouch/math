import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingCoefficientCompactness
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzProductSampling

namespace OAI

/-! # Scalar multiplication and conjugation preserve compact coefficient approximation -/

open Filter Topology
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

variable (a k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
  (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n) (q : ℕ → FourierL2)

theorem ExpandingCompactApproximation.smul
    (hq : ExpandingCompactApproximation a k ha1 hk L hL q) (c : ℂ) :
    ExpandingCompactApproximation a k ha1 hk L hL (fun n => c • q n) := by
  intro ε hε
  let δ := ε / (‖c‖ + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨R, K, hK, herr⟩ := hq δ hδ
  refine ⟨R, c • K, ?_, ?_⟩
  · intro y hy
    simp only [smul_apply, hK y hy, smul_zero]
  · have hbound : ‖c‖ * δ < ε := by
      have hi : δ * (‖c‖ + 1) = ε := div_mul_cancel₀ _ (by positivity)
      nlinarith
    filter_upwards [herr] with n hn
    have he : schwartzTorusSample a k (L n) ha1 hk (hL n) (radianFourierKernel (c • K)) =
        c • schwartzTorusSample a k (L n) ha1 hk (hL n) (radianFourierKernel K) :=
      (physicalSchwartzTorusSamplingLinear a k (L n) ha1 hk (hL n)).map_smul c K
    rw [he, ← smul_sub, norm_smul]
    exact (mul_le_mul_of_nonneg_left hn.le (norm_nonneg c)).trans_lt hbound

include ha in
theorem ExpandingCompactApproximation.conjugate
    (hq : ExpandingCompactApproximation a k ha1 hk L hL q) :
    ExpandingCompactApproximation a k ha1 hk L hL (fun n => fourierConjugate (q n)) := by
  intro ε hε
  obtain ⟨R, K, hK, herr⟩ := hq ε hε
  refine ⟨R, schwartzPointConjugate K, ?_, ?_⟩
  · intro y hy
    simp only [schwartzPointConjugate_apply, hK y hy, map_zero]
  · filter_upwards [herr] with n hn
    rw [← schwartzTorusSample_conjugate a k (L n) ha ha1 hk (hL n)]
    change ‖sobolevConjugation (q n) - sobolevConjugation _‖ < ε
    rw [← map_sub, sobolevConjugation_apply, fourierConjugate_norm]
    exact hn

end DefocusingNLS

end OAI
