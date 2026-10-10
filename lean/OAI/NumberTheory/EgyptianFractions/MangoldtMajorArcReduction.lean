import OAI.NumberTheory.EgyptianFractions.MangoldtMinorArcActual
import OAI.NumberTheory.EgyptianFractions.ThreePrimeAnalyticReduction

namespace OAI
noncomputable section
open Filter MeasureTheory Asymptotics

namespace Problem337.MangoldtMajorArcReduction

open ThreePrimeContinuousFourier MangoldtMinorArcActual

/-- The major arcs complementary to the proved logarithmic minor arcs. -/
def majorArcs (N : ℕ) : Set ℝ :=
  Set.Icc 0 1 ∩ ThreePrimeAnalysis.majorArcUnion
    ⌊Real.log (N : ℝ) ^ 18⌋₊ (2 * Real.log (N : ℝ) ^ 18 / N)

/-- The actual major-arc contribution, not a model exponential sum. -/
def majorIntegral (N : ℕ) : ℂ :=
  ∫ x in majorArcs N, mangoldtPhaseSum N x ^ 3 * phase (-(N : ℤ)) x

lemma measurableSet_majorArcs (N : ℕ) : MeasurableSet (majorArcs N) :=
  measurableSet_Icc.inter (ThreePrimeAnalysis.measurableSet_majorArcUnion _ _)

/-- Exact major/minor decomposition of the actual arithmetic coefficient. -/
theorem mangoldt_coefficient_eq_major_add_minor (N : ℕ) :
    (mangoldtTripleSum N : ℂ) = majorIntegral N +
      ∫ x in minorArcs 3 N, mangoldtPhaseSum N x ^ 3 * phase (-(N : ℤ)) x := by
  have hf : IntegrableOn
      (fun x => mangoldtPhaseSum N x ^ 3 * phase (-(N : ℤ)) x) (Set.Icc 0 1) :=
    ((mangoldtPhaseSum_continuous N).pow 3 |>.mul
      (phase_continuous _)).integrableOn_Icc
  have hsplit := integral_inter_add_sdiff
    (ThreePrimeAnalysis.measurableSet_majorArcUnion
      ⌊Real.log (N : ℝ) ^ 18⌋₊ (2 * Real.log (N : ℝ) ^ 18 / N)) hf
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    mangoldt_triple_integral] at hsplit
  exact hsplit.symm

theorem mangoldt_coefficient_sub_major (N : ℕ) :
    (mangoldtTripleSum N : ℂ) - majorIntegral N =
      ∫ x in minorArcs 3 N, mangoldtPhaseSum N x ^ 3 * phase (-(N : ℤ)) x := by
  rw [mangoldt_coefficient_eq_major_add_minor]
  ring

/-- The actual major integral approximates the arithmetic coefficient with
an unconditional little-oh quadratic error. -/
theorem mangoldt_coefficient_sub_major_isLittleO :
    (fun N : ℕ => (mangoldtTripleSum N : ℂ) - majorIntegral N) =o[atTop]
      (fun N : ℕ => (N : ℝ) ^ 2) := by
  simpa only [mangoldt_coefficient_sub_major] using mangoldt_minor_integral_isLittleO

/-- A positive quadratic lower bound on the actual major contribution alone
now suffices. There is no remaining minor-arc analytic hypothesis. -/
theorem quantitativeThreePrimeLowerBound_of_major_lower
    (hmajor : ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, Odd N →
      c * (N : ℝ) ^ 2 ≤ (majorIntegral N).re) :
    QuantitativeThreePrimeLowerBound := by
  obtain ⟨c, hc, hmajor⟩ := hmajor
  apply quantitativeThreePrimeLowerBound_of_mangoldt
  refine ⟨c / 2, by positivity, ?_⟩
  filter_upwards [hmajor, eventually_mangoldt_minor_integral_small (c / 2) (by positivity)]
    with N hmajor hminor
  intro hodd
  have herror : |mangoldtTripleSum N - (majorIntegral N).re| ≤ (c / 2) * (N : ℝ) ^ 2 := by
    have h := Complex.abs_re_le_norm ((mangoldtTripleSum N : ℂ) - majorIntegral N)
    simp only [Complex.sub_re, Complex.ofReal_re] at h
    exact h.trans (by simpa only [mangoldt_coefficient_sub_major] using hminor)
  have hlow := (abs_le.mp herror).1
  have hm := hmajor hodd
  linarith

/-- The full ternary asymptotic follows from its major-arc part alone, since
the actual minor integral has already been estimated unconditionally. -/
theorem ternaryMangoldtAsymptotic_of_major_asymptotic
    (hmajor : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, Odd N →
      ‖majorIntegral N -
        (((1 / 2 : ℝ) * threePrimeSingularSeries N * (N : ℝ) ^ 2 : ℝ) : ℂ)‖ ≤
        ε * (N : ℝ) ^ 2) : TernaryMangoldtAsymptotic := by
  intro ε hε
  filter_upwards [hmajor (ε / 2) (by positivity),
    eventually_mangoldt_minor_integral_small (ε / 2) (by positivity)] with N hmajor hminor
  intro hodd
  have hnorm : ‖(mangoldtTripleSum N : ℂ) -
      (((1 / 2 : ℝ) * threePrimeSingularSeries N * (N : ℝ) ^ 2 : ℝ) : ℂ)‖ ≤
      ε * (N : ℝ) ^ 2 := by
    calc
      _ ≤ ‖(mangoldtTripleSum N : ℂ) - majorIntegral N‖ +
          ‖majorIntegral N -
            (((1 / 2 : ℝ) * threePrimeSingularSeries N * (N : ℝ) ^ 2 : ℝ) : ℂ)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (ε / 2) * (N : ℝ) ^ 2 + (ε / 2) * (N : ℝ) ^ 2 :=
        add_le_add (by simpa only [mangoldt_coefficient_sub_major] using hminor) (hmajor hodd)
      _ = _ := by ring
  simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hnorm

end Problem337.MangoldtMajorArcReduction

end

end OAI
