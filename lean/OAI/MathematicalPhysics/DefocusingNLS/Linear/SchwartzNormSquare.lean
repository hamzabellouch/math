import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousDerivativeConjugation
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzSeparatedPeriodization

namespace OAI

/-! # Squared moduli as Schwartz functions and separated periodizations -/

open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def schwartzNormSquare (K : 𝓢(E, ℂ)) : 𝓢(E, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (homogeneousPhysicalSchwartzStar K) K

@[simp] theorem schwartzNormSquare_apply (K : 𝓢(E, ℂ)) (x : E) :
    schwartzNormSquare K x = (‖K x‖ ^ 2 : ℝ) := by
  rw [schwartzNormSquare, SchwartzMap.smulLeftCLM_apply_apply
    (homogeneousPhysicalSchwartzStar K).hasTemperateGrowth,
    homogeneousPhysicalSchwartzStar_apply, smul_eq_mul, mul_comm]
  simpa only [Complex.sq_norm, Complex.star_def] using Complex.mul_conj (K x)

theorem periodizationRescale_normSquare (L : ℝ) (hL : 0 < L) (K : 𝓢(E, ℂ)) :
    periodizationRescale L hL (schwartzNormSquare K) =
      schwartzNormSquare (periodizationRescale L hL K) := by
  ext x
  simp only [periodizationRescale_apply, schwartzNormSquare_apply]

theorem separatedSchwartz_periodization_normSquare (L R : ℝ) (hL : 0 < L)
    (hLR : 2 * R < 2 * Real.pi * L) (K : 𝓢(E, ℂ))
    (hK : ∀ x : E, R < ‖x‖ → K x = 0) (x : E) :
    schwartzPeriodization (periodizationRescale L hL (schwartzNormSquare K)) x =
      (‖schwartzPeriodization (periodizationRescale L hL K) x‖ ^ 2 : ℝ) := by
  have he := separatedSchwartz_norm_tsum_sq (2 * Real.pi * L) R (by positivity) hLR K hK
    ((2 * Real.pi * L) • x)
  simp only [schwartzPeriodization_apply, periodizationRescale_apply, schwartzNormSquare_apply,
    smul_add]
  rw [he, Complex.ofReal_tsum]

end DefocusingNLS

end OAI
