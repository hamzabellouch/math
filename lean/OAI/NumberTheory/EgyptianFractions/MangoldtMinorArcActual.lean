import OAI.NumberTheory.EgyptianFractions.MinorArcVaughan
import OAI.NumberTheory.EgyptianFractions.ThreePrimeContinuousEnergy
import OAI.NumberTheory.EgyptianFractions.ThreePrimeMangoldtIntegral

namespace OAI
noncomputable section
open scoped BigOperators
open Filter MeasureTheory

namespace Problem337.MangoldtMinorArcActual

open ThreePrimeContinuousFourier

/-- The logarithmic minor arcs, with the denominator cutoff needed to save
`D` powers of the logarithm in the actual Mangoldt exponential sum. -/
def minorArcs (D N : ℕ) : Set ℝ :=
  Set.Icc 0 1 \ ThreePrimeAnalysis.majorArcUnion
    ⌊Real.log (N : ℝ) ^ (2 * (4 + D + 2))⌋₊
    (2 * Real.log (N : ℝ) ^ (2 * (4 + D + 2)) / N)

lemma measurableSet_minorArcs (D N : ℕ) : MeasurableSet (minorArcs D N) :=
  measurableSet_Icc.diff (ThreePrimeAnalysis.measurableSet_majorArcUnion _ _)

lemma minorArcs_subset (D N : ℕ) : minorArcs D N ⊆ Set.Icc 0 1 :=
  Set.sdiff_subset

/-- The two independently developed Fourier conventions agree exactly. -/
lemma phase_eq_vaughan (n : ℕ) (x : ℝ) :
    phase (n : ℤ) x = VaughanBilinear.phase (x * n) := by
  rw [phase_exp]
  simp only [VaughanBilinear.phase, Real.fourierChar_apply]
  congr 1
  push_cast
  ring

lemma mangoldtPhaseSum_eq_weightedSum (N : ℕ) (x : ℝ) :
    mangoldtPhaseSum N x = Vaughan.weightedSum (Finset.Ioc 0 N)
      (fun n => VaughanBilinear.phase (x * n)) ArithmeticFunction.vonMangoldt := by
  have hset : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  simp only [mangoldtPhaseSum, Vaughan.weightedSum, phase_eq_vaughan, hset]

/-- Actual minor-arc cancellation. The pointwise exponential-sum estimate is
proved, not assumed: it combines Vaughan's estimate with Dirichlet geometry. -/
theorem eventually_mangoldtPhaseSum_norm_le (D : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ x ∈ minorArcs D N,
      ‖mangoldtPhaseSum N x‖ ≤ (N : ℝ) / Real.log (N : ℝ) ^ D := by
  filter_upwards [MinorArc.eventually_vonMangoldt_minor_arc_bound D] with N hbound
  intro x hx
  rw [mangoldtPhaseSum_eq_weightedSum]
  exact hbound x hx.1 hx.2

/-- A crude but unconditional coefficient energy bound is sufficient once
three logarithmic powers have been saved pointwise. -/
lemma mangoldt_square_sum_le (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ ^ 2) ≤
      (N : ℝ) * Real.log (N : ℝ) ^ 2 := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N, Real.log (N : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      have hn1 : 0 < (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      have hnN : (n : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hn).2
      have hΛ : ArithmeticFunction.vonMangoldt n ≤ Real.log (N : ℝ) :=
        ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hn1 hnN)
      simpa only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg] using
        pow_le_pow_left₀ ArithmeticFunction.vonMangoldt_nonneg hΛ 2
    _ = _ := by simp

lemma mangoldtPhaseSum_eq_natPolynomial (N : ℕ) (x : ℝ) :
    mangoldtPhaseSum N x = ThreePrimeContinuousEnergy.natPolynomial
      (Finset.Icc 1 N) (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) x := by
  exact mangoldtPhaseSum_exp N x

/-- On the explicit logarithmic minor arcs the actual cubic extraction
integral is at most `N²/log N`, without a prime-distribution hypothesis. -/
theorem eventually_mangoldt_minor_integral_le :
    ∀ᶠ N : ℕ in atTop,
      ‖∫ x in minorArcs 3 N, mangoldtPhaseSum N x ^ 3 * phase (-(N : ℤ)) x‖ ≤
        (N : ℝ) ^ 2 / Real.log (N : ℝ) := by
  filter_upwards [eventually_mangoldtPhaseSum_norm_le 3, eventually_ge_atTop 2]
    with N hminor hN
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hB : 0 ≤ (N : ℝ) / Real.log (N : ℝ) ^ 3 := by positivity
  have h := ThreePrimeContinuousEnergy.nat_polynomial_interval_minor_cubic_bound
    (Finset.Icc 1 N) (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
    (phase (-(N : ℤ))) (minorArcs 3 N) (measurableSet_minorArcs 3 N)
    (minorArcs_subset 3 N) ((N : ℝ) / Real.log (N : ℝ) ^ 3) hB
    (by simpa only [← mangoldtPhaseSum_eq_natPolynomial] using hminor)
    (by intro x hx; exact (norm_phase _ _).le)
  simp only [← mangoldtPhaseSum_eq_natPolynomial] at h
  refine h.trans ((mul_le_mul_of_nonneg_left (mangoldt_square_sum_le N) hB).trans ?_)
  exact le_of_eq (by field_simp)

/-- The minor arcs contribute an arbitrarily small quadratic error. Their
cutoff is fixed at `log(N)^18`, independently of the requested error. -/
theorem eventually_mangoldt_minor_integral_small (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      ‖∫ x in minorArcs 3 N, mangoldtPhaseSum N x ^ 3 * phase (-(N : ℤ)) x‖ ≤
        ε * (N : ℝ) ^ 2 := by
  have hlog : ∀ᶠ N : ℕ in atTop, 1 / ε ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1 / ε))
  filter_upwards [eventually_mangoldt_minor_integral_le, hlog] with N hN hlog
  have hL : 0 < Real.log (N : ℝ) := (one_div_pos.mpr hε).trans_le hlog
  have hcoef : 1 ≤ ε * Real.log (N : ℝ) := (div_le_iff₀ hε).mp hlog |>.trans_eq (mul_comm _ _)
  apply hN.trans
  apply (div_le_iff₀ hL).mpr
  nlinarith [mul_le_mul_of_nonneg_right hcoef (sq_nonneg (N : ℝ))]

/-- Standard little-oh form of the unconditional minor-arc estimate. -/
theorem mangoldt_minor_integral_isLittleO :
    (fun N : ℕ => ∫ x in minorArcs 3 N,
      mangoldtPhaseSum N x ^ 3 * phase (-(N : ℤ)) x) =o[atTop]
        (fun N : ℕ => (N : ℝ) ^ 2) := by
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  filter_upwards [eventually_mangoldt_minor_integral_small ε hε] with N hN
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (N : ℝ))] using hN

end Problem337.MangoldtMinorArcActual

end

end OAI
