import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingFilteredDerivatives

namespace OAI

/-! # Filtered derivative limits from the actual weak localization limit -/

open Filter Topology
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def homogeneousPhysicalContinuous (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (v : HomogeneousY a k) : C(E, ℂ) :=
  (homogeneousPhysicalCLM a k ha ha1 hk v).toContinuousMap

theorem homogeneousPhysicalContinuous_bound (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (v : HomogeneousY a k) (y : E) :
    ‖homogeneousPhysicalContinuous a k ha ha1 hk v y‖ ≤ ‖homogeneousPhysicalCLM a k ha ha1 hk v‖ := by
  have h := (homogeneousPhysicalCLM a k ha ha1 hk v).toBCF.norm_coe_le_norm y
  change ‖homogeneousPhysicalCLM a k ha ha1 hk v y‖ ≤
    ‖homogeneousPhysicalCLM a k ha ha1 hk v‖ at h
  exact h

theorem expandingFilteredDerivative_of_localized_weak (a k M B R S : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n) (hLinf : Tendsto L atTop atTop)
    (χ : 𝓢(E, ℂ)) (ρ : ℝ) (hρ : 0 < ρ) (hχ : ∀ y : E, ‖y‖ ≤ ρ → χ y = 1)
    (f : ℕ → FourierL2) (hf : ∀ n, ‖f n‖ ≤ M) (v : HomogeneousY a k)
    (hbound : ∀ n, ‖homogeneousLocalizationCLM a k (L n) ha ha1 hk (hL n) χ (f n)‖ ≤ B)
    (hweak : ∀ ℓ : HomogeneousY a k →L[ℝ] ℂ,
      Tendsto (fun n => ℓ (homogeneousLocalizationCLM a k (L n) ha ha1 hk (hL n) χ (f n)))
        atTop (𝓝 (ℓ v))) (hS : 0 < S) (N : ℕ) (j : Fin N → Fin 12) :
    Tendsto (fun n => expandingPhysicalBall a k (L n) R ha ha1 hk (hL n)
      (expandingSmoothDerivative (L n) S hS N j (f n))) atTop
      (𝓝 (schwartzBallConvolution R (smoothDerivativeKernel S hS N j)
        (homogeneousPhysicalContinuous a k ha ha1 hk v))) := by
  apply tendsto_expandingSmoothDerivative_local a k M
    ‖homogeneousPhysicalCLM a k ha ha1 hk v‖ R S ha ha1 hk
    ((norm_nonneg (f 0)).trans (hf 0)) (norm_nonneg _) hS N j L hL f hf
    (homogeneousPhysicalContinuous a k ha ha1 hk v)
    (homogeneousPhysicalContinuous_bound a k ha ha1 hk v)
  exact expandingTorus_local_uniform_of_localized_weak a k B ha ha1 hk L hL hLinf
    χ ρ hρ hχ f v hbound hweak

end DefocusingNLS

end OAI
