import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingFilteredLimit
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousCommutatorSymbol

namespace OAI

/-! # Ordered frequency derivatives of the compactly filtered torus field -/

open Filter Topology MeasureTheory
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def smoothDerivativeKernel (R : ℝ) (hR : 0 < R) (N : ℕ)
    (j : Fin N → Fin 12) : 𝓢(E, ℂ) :=
  homogeneousOrderedDerivative N j (radianInverseKernel (smoothFrequencyCutoff R hR))

theorem smoothDerivativeKernel_fourier (R : ℝ) (hR : 0 < R) (N : ℕ)
    (j : Fin N → Fin 12) (ξ : E) :
    radianFourierKernel (smoothDerivativeKernel R hR N j) ξ =
      homogeneousOrderedSymbol N j ξ * smoothFrequencyCutoff R hR ξ := by
  rw [smoothDerivativeKernel, homogeneousOrderedDerivative_fourier,
    radianFourierKernel_inverseKernel]
  rfl

noncomputable def expandingSmoothDerivative (L R : ℝ) (hR : 0 < R) (N : ℕ)
    (j : Fin N → Fin 12) : FourierL2 →L[ℂ] FourierL2 :=
  expandingSchwartzFilter L (smoothDerivativeKernel R hR N j)

@[simp] theorem expandingSmoothDerivative_apply (L R : ℝ) (hR : 0 < R) (N : ℕ)
    (j : Fin N → Fin 12) (f : FourierL2) (n : frequencyLattice) :
    expandingSmoothDerivative L R hR N j f n =
      (homogeneousOrderedSymbol N j (L⁻¹ • (n : E)) *
        smoothFrequencyCutoff R hR (L⁻¹ • (n : E))) * f n := by
  rw [expandingSmoothDerivative, expandingSchwartzFilter_apply, smoothDerivativeKernel_fourier]

theorem expandingSmoothDerivative_physical (a k L R : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hR : 0 < R)
    (N : ℕ) (j : Fin N → Fin 12) (f : FourierL2) (y : E) :
    expandingPhysicalContinuous a k L ha ha1 hk hL (expandingSmoothDerivative L R hR N j f) y =
      ∫ z : E, smoothDerivativeKernel R hR N j z *
        expandingPhysicalContinuous a k L ha ha1 hk hL f (y - z) :=
  expandingSchwartzFilter_physical a k L ha ha1 hk hL _ f y

theorem expandingSmoothDerivative_physical_bound (a k L R : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hR : 0 < R)
    (N : ℕ) (j : Fin N → Fin 12) (f : FourierL2) (y : E) :
    ‖expandingPhysicalContinuous a k L ha ha1 hk hL (expandingSmoothDerivative L R hR N j f) y‖ ≤
      expandingEmbeddingBound a k * (∫ z : E, ‖smoothDerivativeKernel R hR N j z‖) * ‖f‖ := by
  refine (expandingPhysicalContinuous_norm_le a k L ha ha1 hk hL _ y).trans ?_
  have h := fourierBoundedMultiplier_norm_le
    (∫ z : E, ‖smoothDerivativeKernel R hR N j z‖)
    (integral_nonneg (fun _ => norm_nonneg _))
    (fun n : frequencyLattice => radianFourierKernel (smoothDerivativeKernel R hR N j)
      (L⁻¹ • (n : E))) (fun _ => radianFourierKernel_norm_le_integral _ _) f
  exact (mul_le_mul_of_nonneg_left h
    (by unfold expandingEmbeddingBound; positivity)).trans_eq (mul_assoc _ _ _).symm

theorem tendsto_expandingSmoothDerivative_local (a k M M₀ R S : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hM : 0 ≤ M) (hM₀ : 0 ≤ M₀) (hS : 0 < S)
    (N : ℕ) (j : Fin N → Fin 12) (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n)
    (f : ℕ → FourierL2) (hf : ∀ n, ‖f n‖ ≤ M) (v : C(E, ℂ)) (hv : ∀ y, ‖v y‖ ≤ M₀)
    (hlocal : ∀ T ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ y : E, ‖y‖ ≤ T →
      ‖expandingTorusFunction a k (L n) (f n) (euclideanToTorus ((L n)⁻¹ • y)) - v y‖ < ε) :
    Tendsto (fun n => expandingPhysicalBall a k (L n) R ha ha1 hk (hL n)
      (expandingSmoothDerivative (L n) S hS N j (f n))) atTop
        (𝓝 (schwartzBallConvolution R (smoothDerivativeKernel S hS N j) v)) :=
  tendsto_expandingPhysicalBall_filter a k M M₀ R ha ha1 hk hM hM₀ L hL _ f hf v hv hlocal

end DefocusingNLS

end OAI
