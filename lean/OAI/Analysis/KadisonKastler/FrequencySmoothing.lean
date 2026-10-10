import OAI.Analysis.KadisonKastler.FrequencyCovariance
import OAI.Analysis.KadisonKastler.DemodulatedInverseBounds
import OAI.Analysis.KadisonKastler.AnalyticAlgebraBounds

namespace OAI

/-! # Actual smoothing from quantitative frequency-cut defects

The boundary approximants are constructed by the published nest distance
theorem and the proved invariant averaging. The smoothing operators are
their actual Poisson integrals; their inverse and algebra estimates use
the published Hardy evaluation, with no additional analytic identities.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance frequencySmoothingOrder (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance frequencySmoothingStarOrder (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

/-- The precise output of frequency-nest approximation for a contraction
field. The approximation is on the common original Hilbert space. -/
structure FrequencySmoothing (F : ℝ → H →L[ℂ] H) (δ : ℝ) where
  boundary : ℝ → H →L[ℂ] H
  measurable : ∀ x, AEStronglyMeasurable (fun t => boundary t x) volume
  bounded : ∀ᵐ t, ‖boundary t‖ ≤ 1 + 2 * δ
  close : ∀ᵐ t, ‖boundary t - F t‖ ≤ 2 * δ
  preserves : PreservesProjectionNest (regularFrequencyNest (H := H))
    (regularFieldOperator volume boundary measurable (1 + 2 * δ) bounded)

theorem exists_frequencySmoothing [TopologicalSpace.SeparableSpace H]
    (hNest : PublishedRealNestDistance.{u})
    (hSpectral : PublishedRealSpectralCommutant.{u})
    (hDiagonal : PublishedRealDiagonalDecomposition.{u})
    (F : ℝ → H →L[ℂ] H)
    (hF : ∀ x, AEStronglyMeasurable (fun t => F t x) volume)
    (hb : ∀ᵐ t, ‖F t‖ ≤ 1) {δ : ℝ} (hδ : 0 < δ)
    (hdefect : ∀ a, ‖(1 - regularFrequencyNest a) *
      regularFieldOperator volume F hF 1 hb * regularFrequencyNest a‖ ≤ δ) :
    Nonempty (FrequencySmoothing F δ) := by
  obtain ⟨B, S, hS, hB, hBS, hBn, hBF⟩ :=
    exists_frequency_nest_multiplier hNest hSpectral hDiagonal F hF zero_le_one hb hδ hdefect
  have he := RepresentsOperatorField.unique hBS
    (regularFieldOperator_represents volume B hB (1 + 2 * δ) hBn)
  rw [he] at hS
  exact ⟨⟨B, hB, hBn, hBF, hS⟩⟩

namespace FrequencySmoothing

variable {F G : ℝ → H →L[ℂ] H} {δ : ℝ}

/-- Positive-height smoothing after removing the scalar modulation. -/
def smooth (A : FrequencySmoothing F δ) (t r : ℝ) (hr : 0 < r) : H →L[ℂ] H :=
  demodulatedPoissonAverage A.boundary A.measurable (1 + 2 * δ) A.bounded t r hr

theorem continuous_smooth (A : FrequencySmoothing F δ) (hδ : 0 ≤ δ)
    (r : ℝ) (hr : 0 < r) : Continuous (fun t => A.smooth t r hr) :=
  continuous_demodulatedPoissonAverage A.boundary A.measurable (by positivity) A.bounded r hr

theorem norm_smooth_le (A : FrequencySmoothing F δ) (hδ : 0 ≤ δ)
    (t r : ℝ) (hr : 0 < r) : ‖A.smooth t r hr‖ ≤ Real.exp r * (1 + 2 * δ) :=
  norm_demodulatedPoissonAverage_le A.boundary A.measurable (by positivity) A.bounded t r hr

theorem norm_smooth_le_one_add (A : FrequencySmoothing F δ)
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 8)
    (t r : ℝ) (hr : 0 < r) (hrδ : r ≤ δ) : ‖A.smooth t r hr‖ ≤ 1 + 5 * δ := by
  have habs : |r| ≤ 1 := by rw [abs_of_pos hr]; linarith
  have he := Real.abs_exp_sub_one_le habs
  rw [abs_of_pos hr] at he
  have he' : Real.exp r ≤ 1 + 2 * δ := by
    linarith [le_abs_self (Real.exp r - 1)]
  exact (A.norm_smooth_le hδ t r hr).trans
    ((mul_le_mul_of_nonneg_right he' (by positivity)).trans (by nlinarith))

theorem norm_product_sub_one_le [TopologicalSpace.SeparableSpace H]
    (hHardy : PublishedHardyMultiplierEvaluation.{u})
    (A : FrequencySmoothing F δ) (B : FrequencySmoothing G δ)
    (hF : ∀ x, AEStronglyMeasurable (fun t => F t x) volume)
    (hG : ∀ x, AEStronglyMeasurable (fun t => G t x) volume)
    (hFn : ∀ᵐ t, ‖F t‖ ≤ 1) (hGn : ∀ᵐ t, ‖G t‖ ≤ 1)
    (hFG : ∀ᵐ t, F t * G t = poissonCharacterField 2 t)
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 16)
    (t r : ℝ) (hr : 0 < r) (hrδ : r ≤ δ) :
    ‖A.smooth t r hr * B.smooth t r hr - 1‖ ≤ 12 * δ := by
  have hab : ∀ᵐ s, ‖A.boundary s * B.boundary s‖ ≤ (1 + 2 * δ) * (1 + 2 * δ) := by
    filter_upwards [A.bounded, B.bounded] with s ha hb
    exact (norm_mul_le _ _).trans (mul_le_mul ha hb (norm_nonneg _) (by positivity))
  have hfg : ∀ᵐ s, ‖F s * G s‖ ≤ 1 := by
    filter_upwards [hFn, hGn] with s hf hg
    exact (norm_mul_le _ _).trans ((mul_le_mul hf hg (norm_nonneg _) zero_le_one).trans_eq
      (one_mul 1))
  have hi := norm_demodulatedPoisson_product_sub_one_le hHardy A.boundary B.boundary F G
    A.measurable B.measurable hF hG A.bounded B.bounded hab hfg
    (show 0 ≤ 2 * δ by positivity) hFn hGn A.close B.close t r hr A.preserves B.preserves hFG
  exact hi.trans ((exp_two_mul_product_error_le hr.le (by linarith)
    (by positivity) (by linarith : 2 * δ ≤ 1 / 8)).trans_eq (by ring))

/-- Comparison to the original continuous modular field, using the same
boundary Poisson operator that already has strong-star convergence. -/
theorem norm_smooth_sub_boundary_le
    (W : ℝ → unitary (H →L[ℂ] H))
    (A : FrequencySmoothing (modulatedUnitaryField W) δ)
    (hW : ∀ x, Continuous (fun t => (W t : H →L[ℂ] H) x))
    (hδ : 0 ≤ δ) (t r : ℝ) (hr : 0 < r) :
    ‖A.smooth t r hr - poissonBoundaryApprox W hW t r‖ ≤ Real.exp r * (2 * δ) :=
  norm_demodulatedPoissonAverage_sub_boundary_le A.boundary A.measurable (1 + 2 * δ)
    A.bounded W hW (by positivity) A.close t r hr

theorem norm_smooth_sub_boundary_le_four
    (W : ℝ → unitary (H →L[ℂ] H))
    (A : FrequencySmoothing (modulatedUnitaryField W) δ)
    (hW : ∀ x, Continuous (fun t => (W t : H →L[ℂ] H) x))
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 8)
    (t r : ℝ) (hr : 0 < r) (hrδ : r ≤ δ) :
    ‖A.smooth t r hr - poissonBoundaryApprox W hW t r‖ ≤ 4 * δ := by
  have he := Real.abs_exp_sub_one_le (x := r)
    (show |r| ≤ 1 by rw [abs_of_pos hr]; linarith)
  rw [abs_of_pos hr] at he
  have he' : Real.exp r ≤ 2 := by linarith [le_abs_self (Real.exp r - 1)]
  exact (A.norm_smooth_sub_boundary_le W hW hδ t r hr).trans
    ((mul_le_mul_of_nonneg_right he' (by positivity)).trans_eq (by ring))

theorem infDist_smooth_sandwich_le [TopologicalSpace.SeparableSpace H]
    (hHardy : PublishedHardyMultiplierEvaluation.{u})
    (M : VonNeumannAlgebra H)
    (hDistance : PublishedBlockCommutantApproximation (Algebra M.commutant) H)
    (A : FrequencySmoothing F δ) (B : FrequencySmoothing G δ)
    (hFn : ∀ᵐ t, ‖F t‖ ≤ 1) (hGn : ∀ᵐ t, ‖G t‖ ≤ 1)
    {e : ℝ} (he : 0 ≤ e) (heδ : e ≤ δ)
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 16) (x : H →L[ℂ] H)
    (hnear : ∀ᵐ s, Metric.infDist (F s * x * G s) (M : Set (H →L[ℂ] H)) ≤ e * ‖x‖)
    (t r : ℝ) (hr : 0 < r) (hrδ : r ≤ δ) :
    Metric.infDist (A.smooth t r hr * x * B.smooth t r hr)
      (M : Set (H →L[ℂ] H)) ≤ 12 * δ * ‖x‖ := by
  have hb := infDist_demodulated_sandwich_le hHardy M hDistance
    A.boundary B.boundary F G A.measurable B.measurable
    (show 0 ≤ 1 + 2 * δ by positivity) A.bounded B.bounded
    (show 0 ≤ 2 * δ by positivity) he hFn hGn A.close B.close x hnear t r hr
    A.preserves B.preserves
  have habs : |r| ≤ 1 := by rw [abs_of_pos hr]; linarith
  have hex := Real.abs_exp_sub_one_le habs
  rw [abs_of_pos hr] at hex
  have hex' : Real.exp r ≤ 1 + 2 * δ := by linarith [le_abs_self (Real.exp r - 1)]
  have hex2 : (Real.exp r) ^ 2 ≤ 2 := by
    nlinarith [Real.exp_pos r]
  have herr : e + 2 * (2 * δ) + (2 * δ) ^ 2 ≤ 6 * δ := by nlinarith
  exact hb.trans ((mul_le_mul hex2 (mul_le_mul_of_nonneg_right herr (norm_nonneg x))
    (by positivity) (by norm_num)).trans_eq (by ring))

end FrequencySmoothing

end

end KadisonKastler

end OAI
