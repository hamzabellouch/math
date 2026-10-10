import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalWeakLimit

namespace OAI

/-! # The norm bound retained by a weak homogeneous limit -/

open Filter Topology

namespace DefocusingNLS

theorem homogeneousY_norm_le_of_weak_limit (a k M : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (u : ℕ → HomogeneousY a k) (v : HomogeneousY a k)
    (hu : ∀ n, ‖u n‖ ≤ M)
    (hv : ∀ ℓ : HomogeneousY a k →L[ℝ] ℂ,
      Tendsto (fun n => ℓ (u n)) atTop (𝓝 (ℓ v))) : ‖v‖ ≤ M := by
  obtain ⟨w, hw, φ, hφ, hweak⟩ := homogeneousY_weak_subsequence a k M ha1 hk u hu
  have he : w = v := by
    apply homogeneousPhysicalCLM_injective a k ha ha1 hk
    ext y
    let ℓ := (homogeneousPointEvaluation a k ha ha1 hk y).restrictScalars ℝ
    exact tendsto_nhds_unique (hweak ℓ) ((hv ℓ).comp hφ.tendsto_atTop)
  exact he ▸ hw

end DefocusingNLS

end OAI
