import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzNonlinearPeriodization
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzDyadicCutoff
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.UnitTorusPhysical

namespace OAI

/-! # A scale- and derivative-order independent bound for a sampled cutoff -/

open scoped SchwartzMap ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "T" => UnitAddTorus (Fin 12)

theorem norm_tsum_le_of_disjoint {ι : Type*} (u : ι → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hu : ∀ i, ‖u i‖ ≤ M) (hd : ∀ i j, i ≠ j → u i = 0 ∨ u j = 0) :
    ‖∑' i, u i‖ ≤ M := by
  classical
  by_cases h : ∃ i, u i ≠ 0
  · obtain ⟨i, hi⟩ := h
    have hz (j : ι) (hji : j ≠ i) : u j = 0 := (hd j i hji).resolve_right hi
    rw [tsum_eq_single i hz]
    exact hu i
  · have hz : ∀ i, u i = 0 := by simpa only [not_exists, not_not] using h
    simpa only [hz, tsum_zero, norm_zero] using hM

theorem sampledCutoff_pointwise_bound (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (hχzero : ∀ y : E, 1 ≤ ‖y‖ → χ y = 0)
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (M : ℝ) (hM : 0 ≤ M)
    (hQB : ∀ y : E, ‖Q y‖ ≤ M) (x : T) :
    ‖expandingUnitTorusFunction a k L
      (schwartzTorusSample a k L ha1 hk hL (radianFourierKernel
        (cutoffProfileSchwartz L (by linarith) χ hχ Q hQ))) x‖ ≤
      SchwartzMap.seminorm ℝ 0 0 χ * M := by
  let ψ := cutoffProfileSchwartz L (by linarith : 0 < L) χ hχ Q hQ
  have hψ (y : E) (hy : 2 * L < ‖y‖) : ψ y = 0 := by
    rw [cutoffProfileSchwartz_apply, hχzero, zero_mul]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by linarith))]
    apply (le_inv_mul_iff₀ (by linarith : 0 < L)).mpr
    linarith
  have hb (y : E) : ‖ψ y‖ ≤ SchwartzMap.seminorm ℝ 0 0 χ * M := by
    rw [cutoffProfileSchwartz_apply, norm_mul]
    exact mul_le_mul (SchwartzMap.norm_le_seminorm ℝ χ _) (hQB y) (norm_nonneg _) (by positivity)
  obtain ⟨y, rfl⟩ := unitTorusProjection_isOpenQuotientMap.surjective x
  rw [expandingUnitTorusFunction_projection a k L ha ha1 hk hL]
  have hy : (2 * Real.pi) • y = L⁻¹ • ((2 * Real.pi * L) • y) := by
    rw [smul_smul]
    congr 1
    field_simp
  rw [hy, schwartzTorusSample_physical a k L ha ha1 hk hL]
  exact norm_tsum_le_of_disjoint _ _ (by positivity) (fun n => hb _)
    (cutoff_periodization_disjoint L (by linarith) ψ hψ _)

end DefocusingNLS

end OAI
