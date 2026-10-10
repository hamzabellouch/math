import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzPartialDerivative
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzFrequencyCutoff

namespace OAI

/-! # Concrete partial-derivative kernels for the finite product formula -/

open Set
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def schwartzPartialDerivative (N : ℕ) (j : Fin N → Fin 12)
    (s : Finset (Fin N)) (K : 𝓢(E, ℂ)) : 𝓢(E, ℂ) :=
  Classical.choose (exists_schwartzPartialDerivative N j s K)

theorem schwartzPartialDerivative_fourier (N : ℕ) (j : Fin N → Fin 12)
    (s : Finset (Fin N)) (K : 𝓢(E, ℂ)) (ξ : E) :
    radianFourierKernel (schwartzPartialDerivative N j s K) ξ =
      homogeneousPartialSymbol N j s ξ * radianFourierKernel K ξ :=
  (Classical.choose_spec (exists_schwartzPartialDerivative N j s K)).1 ξ

theorem schwartzPartialDerivative_support (N : ℕ) (j : Fin N → Fin 12)
    (s : Finset (Fin N)) (K : 𝓢(E, ℂ)) :
    tsupport (schwartzPartialDerivative N j s K : E → ℂ) ⊆ tsupport (K : E → ℂ) :=
  (Classical.choose_spec (exists_schwartzPartialDerivative N j s K)).2

theorem schwartzPartialDerivative_zero (N : ℕ) (j : Fin N → Fin 12)
    (s : Finset (Fin N)) (K : 𝓢(E, ℂ)) (R : ℝ)
    (hK : ∀ x : E, R < ‖x‖ → K x = 0) (x : E) (hx : R < ‖x‖) :
    schwartzPartialDerivative N j s K x = 0 := by
  have hball : tsupport (K : E → ℂ) ⊆ Metric.closedBall (0 : E) R := by
    apply closure_minimal ?_ Metric.isClosed_closedBall
    intro y hy
    have hh : ‖y‖ ≤ R := le_of_not_gt (fun h => hy (hK y h))
    simpa only [Metric.mem_closedBall, dist_zero_right] using hh
  by_contra hn
  have hb := hball (schwartzPartialDerivative_support N j s K (subset_closure hn))
  exact (not_le_of_gt hx) (by simpa only [Metric.mem_closedBall, dist_zero_right] using hb)

noncomputable def partialFilterKernel (R : ℝ) (hR : 0 < R) (N : ℕ)
    (j : Fin N → Fin 12) (s : Finset (Fin N)) : 𝓢(E, ℂ) :=
  schwartzPartialDerivative N j s (radianInverseKernel (smoothFrequencyCutoff R hR))

theorem partialFilterKernel_fourier (R : ℝ) (hR : 0 < R) (N : ℕ)
    (j : Fin N → Fin 12) (s : Finset (Fin N)) (ξ : E) :
    radianFourierKernel (partialFilterKernel R hR N j s) ξ =
      homogeneousPartialSymbol N j s ξ * smoothFrequencyCutoff R hR ξ := by
  rw [partialFilterKernel, schwartzPartialDerivative_fourier, radianFourierKernel_inverseKernel]

end DefocusingNLS

end OAI
