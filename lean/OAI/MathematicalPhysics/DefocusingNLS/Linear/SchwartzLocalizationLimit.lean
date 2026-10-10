import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzPeriodizationLimit
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalWeakLimit
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingLocalConvergence
import OAI.MathematicalPhysics.DefocusingNLS.Linear.WeakLinearCoordinates

namespace OAI

/-! # The finite coordinates of a fixed sampled Schwartz function -/

open Filter Topology
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem schwartzSample_localized_weak_limit (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (χ ψ : 𝓢(E, ℂ)) (ρ : ℝ) (hρ : 0 < ρ)
    (hχ : ∀ y : E, ‖y‖ ≤ ρ → χ y = 1)
    (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n) (hLinf : Tendsto L atTop atTop)
    (ℓ : HomogeneousY a k →L[ℝ] ℂ) :
    Tendsto (fun n => ℓ (homogeneousLocalizationCLM a k (L n) ha ha1 hk (hL n) χ
      (schwartzTorusSample a k (L n) ha1 hk (hL n) (radianFourierKernel ψ))))
      atTop (𝓝 (ℓ (homogeneousSchwartzEmbedding a k ha ha1 hk ψ))) := by
  obtain ⟨C, hC, hb⟩ := exists_schwartzTorusSample_norm_bound a k ha1 hk (radianFourierKernel ψ)
  obtain ⟨D, hD, hJ⟩ := exists_homogeneousLocalization_bound a k ha ha1 hk χ
  apply homogeneousY_weak_of_physical_limit a k (D * C) ha ha1 hk
    (hu := fun n => (hJ _ (hL n) _).trans (mul_le_mul_of_nonneg_left (hb _ (hL n)) hD))
  intro y
  rw [homogeneousPhysicalCLM_Schwartz]
  have hp := tendsto_schwartz_periodization ψ y L hL hLinf
  apply hp.congr'
  filter_upwards [eventually_expandingCutoff_one L hL hLinf χ ρ ‖y‖ hρ hχ] with n hn
  change (∑' m : frequencyLattice, ψ (y + (2 * Real.pi * L n) • (m : E))) =
    homogeneousPhysicalCLM a k ha ha1 hk
      (homogeneousLocalizationCLM a k (L n) ha ha1 hk (hL n) χ
        (schwartzTorusSample a k (L n) ha1 hk (hL n) (radianFourierKernel ψ))) y
  rw [homogeneousLocalization_physical, expandingPhysicalLocalization,
    hn y le_rfl, one_mul, schwartzTorusSample_physical a k (L n) ha ha1 hk (hL n)]

theorem schwartzSample_finite_coordinate_limit {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (a k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (χ ψ : 𝓢(E, ℂ)) (ρ : ℝ) (hρ : 0 < ρ)
    (hχ : ∀ y : E, ‖y‖ ≤ ρ → χ y = 1)
    (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n) (hLinf : Tendsto L atTop atTop)
    (π : HomogeneousY a k →L[ℝ] F) :
    Tendsto (fun n => π (homogeneousLocalizationCLM a k (L n) ha ha1 hk (hL n) χ
      (schwartzTorusSample a k (L n) ha1 hk (hL n) (radianFourierKernel ψ))))
      atTop (𝓝 (π (homogeneousSchwartzEmbedding a k ha ha1 hk ψ))) := by
  exact tendsto_finite_coordinates_of_weak π _ _
    (schwartzSample_localized_weak_limit a k ha ha1 hk χ ψ ρ hρ hχ L hL hLinf)

end DefocusingNLS

end OAI
