import OAI.Analysis.Pureness.Projections.FiniteSpectralIntegralRootLimit
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
variable {D : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

theorem positive_cut_continuous (ε : ℝ≥0) : Continuous (Positive.cut (A := D) ε) := by
  apply Continuous.subtype_mk
  apply continuous_iff_continuousAt.mpr
  intro M
  have hnorm : ∀ᶠ N : Positive D in 𝓝 M, ‖N.1‖ < ‖M.1‖+1 :=
    (continuous_subtype_val.norm.continuousAt.tendsto.eventually (gt_mem_nhds (by linarith)))
  have hs : ∀ᶠ N : Positive D in 𝓝 M, quasispectrum ℝ N.1 ⊆ Icc (-(‖M.1‖+1)) (‖M.1‖+1) := by
    filter_upwards [hnorm] with N hN
    intro t ht
    have h := NonUnitalIsometricContinuousFunctionalCalculus.norm_quasispectrum_le N.1 ht
      (IsSelfAdjoint.of_nonneg N.2)
    rw [Real.norm_eq_abs] at h
    exact abs_le.mp (h.trans hN.le)
  exact continuous_subtype_val.continuousAt.cfcₙ isCompact_Icc (fun t : ℝ => max (t-ε) 0)
    hs (Eventually.of_forall (fun N => IsSelfAdjoint.of_nonneg N.2))

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem finiteSpectralIntegral_lowerSemicontinuous
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (hlsc : ∀ n, LowerSemicontinuous (fun M : Positive (FinMatrix A n) => d (finitePositiveClass n M)))
    (n : ℕ) : LowerSemicontinuous (finiteSpectralIntegral d n) := by
  apply lowerSemicontinuous_iff_le_liminf.mpr
  intro M
  calc
    finiteSpectralIntegral d n M ≤ ∫⁻ t in Ioi (0 : ℝ),
        liminf (fun N : Positive (FinMatrix A n) => finiteDimensionDistribution d n N t) (𝓝 M) := by
      apply lintegral_mono
      intro t
      exact ((hlsc n).comp (positive_cut_continuous t.toNNReal)).le_liminf M
    _ ≤ liminf (finiteSpectralIntegral d n) (𝓝 M) :=
      lintegral_liminf_le (fun N => finiteDimensionDistribution_measurable d hd n N)

theorem regularizedFiniteDimension_integral_lowerSemicontinuous
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d) (n : ℕ) :
    LowerSemicontinuous (finiteSpectralIntegral (regularizedFiniteDimension d hd) n) := by
  apply finiteSpectralIntegral_lowerSemicontinuous _ (regularizedFiniteDimension_monotone d hd)
  intro m
  simpa only [regularizedFiniteDimension_eval] using finiteRegularizedValue_lowerSemicontinuous d hd m
end CuntzPureness

end

end OAI
