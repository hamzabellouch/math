import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzProfileSampling

namespace OAI

/-! # Uniform norm bounds for every annulus of the physical cutoff profile -/

open scoped SchwartzMap ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem cutoffOuterAnnulus_decay (a L R : ℝ) (ha : 0 < a)
    (hL : 0 < L) (hR : 0 < R) (hR2 : R ≤ 2 * L) :
    L ^ (-a) ≤ 2 ^ a * R ^ (-a) := by
  have hp : (R / L) ^ a ≤ (2 : ℝ) ^ a :=
    Real.rpow_le_rpow (by positivity) ((div_le_iff₀ hL).mpr hR2) ha.le
  have he : (R / L) ^ a * R ^ (-a) = L ^ (-a) := by
    rw [Real.div_rpow hR.le hL.le, Real.rpow_neg hR.le, Real.rpow_neg hL.le]
    field_simp
  exact he.symm.trans_le (mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hR.le _))

theorem exists_cutoffAnnulus_uniform_bound (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (χ : 𝓢(E, ℂ)) (hχzero : ∀ y : E, 1 ≤ ‖y‖ → χ y = 0) :
    ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
      (D : ℝ), 0 ≤ D →
      (∀ n ≤ N, ∀ y : E, y ≠ 0 →
        ‖iteratedFDeriv ℝ n Q y‖ ≤ D * ‖y‖ ^ (-2 * a - (n : ℝ))) →
      ∀ (L R : ℝ) (hL : 1 ≤ L) (hR : 1 ≤ R),
        ‖schwartzTorusSample a k L ha1 hk hL (radianFourierKernel
          (schwartzPhysicalDilation a R (by linarith)
            (cutoffProfileAnnulus a R L χ homogeneousAnnulusCutoff
              homogeneousAnnulusCutoff_hasCompactSupport Q hQ)))‖ ≤ C * D * R ^ (-a) := by
  obtain ⟨N₁, C₁, hC₁, hb₁⟩ := exists_cutoffProfileAnnulus_sampling_bound a k ha ha1 hk
    χ homogeneousAnnulusCutoff homogeneousAnnulusCutoff_hasCompactSupport homogeneousAnnulusCutoff_support
  obtain ⟨N₂, C₂, hC₂, hb₂⟩ := exists_outerCutoffAnnulus_sampling_bound a k ha ha1 hk
    χ homogeneousAnnulusCutoff homogeneousAnnulusCutoff_hasCompactSupport homogeneousAnnulusCutoff_support
  let C := max C₁ (2 ^ a * C₂)
  have hC : 0 ≤ C := hC₁.trans (le_max_left _ _)
  refine ⟨max N₁ N₂, C, hC, ?_⟩
  intro Q hQ D hD hsymbol L R hL hR
  by_cases hRL : R ≤ L
  · exact (hb₁ Q hQ D hD (fun n hn => hsymbol n (hn.trans (le_max_left _ _)))
      R L hR hRL).trans (by gcongr; exact le_max_left _ _)
  · by_cases hR2 : R ≤ 2 * L
    · have h := hb₂ Q hQ D hD (fun n hn => hsymbol n (hn.trans (le_max_right _ _)))
        L R hL (le_of_lt (lt_of_not_ge hRL)) hR2
      calc
        _ ≤ C₂ * D * L ^ (-a) := h
        _ ≤ C₂ * D * (2 ^ a * R ^ (-a)) := mul_le_mul_of_nonneg_left
          (cutoffOuterAnnulus_decay a L R ha (by linarith) (by linarith) hR2) (mul_nonneg hC₂ hD)
        _ = (2 ^ a * C₂) * D * R ^ (-a) := by ring
        _ ≤ C * D * R ^ (-a) := by gcongr; exact le_max_right _ _
    · rw [cutoffProfileAnnulus_zero_of_large_radius a R L (by linarith)
        (le_of_lt (lt_of_not_ge hR2)) χ hχzero Q hQ]
      change ‖(physicalSchwartzTorusSamplingLinear a k L ha1 hk hL) 0‖ ≤ _
      rw [map_zero, norm_zero]
      positivity

end DefocusingNLS

end OAI
