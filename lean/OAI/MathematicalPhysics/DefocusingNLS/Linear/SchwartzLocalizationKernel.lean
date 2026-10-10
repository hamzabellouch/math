import OAI.MathematicalPhysics.DefocusingNLS.Certificates.MixedFourierLocalization
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzPeriodization

namespace OAI

/-! # Schwartz kernels in the mixed Fourier localization estimate

The actual localization kernel is the Fourier transform of a smooth cutoff.
Its Bessel-weighted versions remain Schwartz, so the lattice-to-continuum
bound applies at both Sobolev orders used in the manuscript.
-/

open MeasureTheory
open scoped SchwartzMap

namespace DefocusingNLS

/-- Applying any real Bessel weight preserves the Schwartz localization kernel. -/
noncomputable def weightedSchwartzKernel (s : ℝ)
    (K : 𝓢(EuclideanSpace ℝ (Fin 12), ℂ)) : 𝓢(EuclideanSpace ℝ (Fin 12), ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun x : EuclideanSpace ℝ (Fin 12) =>
    (1 + ‖x‖ ^ 2) ^ (s / 2)) K

@[simp] theorem weightedSchwartzKernel_apply (s : ℝ)
    (K : 𝓢(EuclideanSpace ℝ (Fin 12), ℂ)) (x : EuclideanSpace ℝ (Fin 12)) :
    weightedSchwartzKernel s K x = ((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) • K x :=
  SchwartzMap.smulLeftCLM_apply_apply
    (Function.hasTemperateGrowth_one_add_norm_sq_rpow _ _) K x

theorem weightedSchwartzKernel_norm (s : ℝ)
    (K : 𝓢(EuclideanSpace ℝ (Fin 12), ℂ)) (x : EuclideanSpace ℝ (Fin 12)) :
    ‖weightedSchwartzKernel s K x‖ = (1 + ‖x‖ ^ 2) ^ (s / 2) * ‖K x‖ := by
  rw [weightedSchwartzKernel_apply, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]

/-- A concrete Schwartz kernel has a finite mixed L² operator bound. -/
theorem exists_schwartz_mixedFourier_bound
    (K : 𝓢(EuclideanSpace ℝ (Fin 12), ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : Finset frequencyLattice) (v : frequencyLattice → ℂ),
      Integrable (fun x => ‖∑ n ∈ S, v n * K (x - n)‖ ^ 2) ∧
        (∫ x, ‖∑ n ∈ S, v n * K (x - n)‖ ^ 2) ≤ C * ∑ n ∈ S, ‖v n‖ ^ 2 := by
  obtain ⟨C, hC, hperiod⟩ := exists_schwartz_periodization_bound K
  refine ⟨C * ∫ x, ‖K x‖, mul_nonneg hC (integral_nonneg (fun _ => norm_nonneg _)), ?_⟩
  intro S v
  exact mixedFourier_integral_bound S v K K.integrable C hC (hperiod S)

/-- The same estimate applies to every real Sobolev weight of the cutoff kernel. -/
theorem exists_weightedSchwartz_mixedFourier_bound (s : ℝ)
    (K : 𝓢(EuclideanSpace ℝ (Fin 12), ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : Finset frequencyLattice) (v : frequencyLattice → ℂ),
      Integrable (fun x => ‖∑ n ∈ S, v n * weightedSchwartzKernel s K (x - n)‖ ^ 2) ∧
        (∫ x, ‖∑ n ∈ S, v n * weightedSchwartzKernel s K (x - n)‖ ^ 2) ≤
          C * ∑ n ∈ S, ‖v n‖ ^ 2 :=
  exists_schwartz_mixedFourier_bound (weightedSchwartzKernel s K)

end DefocusingNLS

end OAI
