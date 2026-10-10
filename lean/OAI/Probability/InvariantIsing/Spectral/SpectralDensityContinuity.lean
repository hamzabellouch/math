import OAI.Probability.InvariantIsing.Spectral.SpectralOverlapPaths

namespace OAI

/-! A continuous bounded extension of the spectral path density. -/

noncomputable section

open Set Filter
open scoped Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem continuous_projectedResolventDerivative
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1) (a : ι) :
    Continuous (projectedResolventDerivative ρ eig hρ hρsum a) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hc : ContinuousAt (fun _ : ℝ => ρ a) x := continuousAt_const
    apply hc.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hx] with y hy
    simp only [projectedResolventDerivative,
      ite_eq_right (not_lt.mpr (le_of_lt (show y < 0 from hy)))]
  · subst x
    apply continuousAt_iff_continuous_left_right.mpr
    refine ⟨?_, continuousWithinAt_projectedResolventDerivative_zero ρ eig hρ hρsum a⟩
    have hc : ContinuousWithinAt (fun _ : ℝ => ρ a) (Iic 0) 0 := continuousWithinAt_const
    apply hc.congr
    · intro y hy
      simp only [projectedResolventDerivative, ite_eq_right (not_lt.mpr (show y ≤ 0 from hy))]
    · simp only [projectedResolventDerivative, lt_self_iff_false, ite_false]
  · exact continuousAt_projectedResolventDerivative_pos ρ eig hρ hρsum a hx

theorem continuous_spectralPathDensity
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (p : OverlapPath) (a : ι) :
    Continuous (spectralPathDensity ρ eig hρ hρsum p a) :=
  (continuous_projectedResolventDerivative ρ eig hρ hρsum a).comp (continuous_deficit p)

theorem spectralPathDensity_le_one
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (p : OverlapPath) (a : ι) (r : ℝ) :
    spectralPathDensity ρ eig hρ hρsum p a r ≤ 1 :=
  projectedResolventDerivative_le_one ρ eig hρ hρsum a (deficit p r)

end InvariantIsing

end

end OAI
