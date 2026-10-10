import OAI.Geometry.RCD.Heat.HeatConcentration
import OAI.Geometry.RCD.Heat.HeatOverlapKernel

namespace OAI

/-! # An unconditional diagonal lower bound for the heat overlap

Short-time concentration and Cauchy--Schwarz give the lower estimate
before pointwise finiteness of the extended overlap is known. Infinity
is retained explicitly; no zero-valued real conversion is used here.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem heatRadonDensity_setIntegral (t : ℝ) (ht : 0 < t) (x : X) (A : Set X) :
    (∫ y in A, hX.heatRadonDensity hn p t ht x y ∂hausdorff n X) =
      (hX.heatRadonMeasure hn p t ht x).real A :=
  Measure.setIntegral_toReal_rnDeriv (hX.heatRadonMeasure_absolutelyContinuous hn p t ht x) A

theorem heatOverlapKernel_diagonal_lower_from_mass (t : ℝ) (ht : 0 < t) (x : X)
    {A : Set X} (hAf : hausdorff n X A ≠ ∞) (hV : 0 < (hausdorff n X).real A)
    {m : ℝ} (hm : 0 ≤ m) (hmass : m ≤ (hX.heatRadonMeasure hn p t ht x).real A) :
    ENNReal.ofReal (m^2 / (hausdorff n X).real A) ≤ hX.heatOverlapKernel hn p t ht x x := by
  by_cases htop : hX.heatOverlapKernel hn p t ht x x = ∞
  · rw [htop]
    exact le_top
  let μ := hausdorff n X
  let ρ := hX.heatRadonDensity hn p t ht x
  have hρ : Measurable ρ := hX.heatRadonDensity_measurable hn p t ht x
  have he : hX.heatOverlapKernel hn p t ht x x = ∫⁻ y, ENNReal.ofReal ((ρ y)^2) ∂μ := by
    rw [hX.heatOverlapKernel_eq_lintegral hn p t ht x x]
    apply lintegral_congr
    intro y
    rw [pow_two, ENNReal.ofReal_mul (hX.heatRadonDensity_nonneg hn p t ht x y)]
  have hi : Integrable (fun y => (ρ y)^2) μ :=
    ⟨(hρ.pow_const 2).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun y => sq_nonneg (ρ y))).mpr
        (by rw [← he]; exact lt_top_iff_ne_top.mpr htop)⟩
  have hmem : MemLp ρ 2 μ := (memLp_two_iff_integrable_sq hρ.aestronglyMeasurable).mpr hi
  let : IsFiniteMeasure (μ.restrict A) := ⟨by simpa using hAf.lt_top⟩
  have hcs := integral_mul_sq_le_integral_sq (μ.restrict A) ρ (fun _ => (1 : ℝ))
    (hmem.mono_measure Measure.restrict_le_self) (memLp_const 1)
  simp only [mul_one, one_pow, integral_const, smul_eq_mul, sq_abs,
    measureReal_restrict_apply MeasurableSet.univ, univ_inter] at hcs
  have hmass' : m ≤ ∫ y in A, ρ y ∂μ := by
    rw [hX.heatRadonDensity_setIntegral hn p t ht x A]
    exact hmass
  have hsquare : m^2 ≤ (∫ y in A, ρ y ∂μ)^2 := pow_le_pow_left₀ hm hmass' 2
  have hglobal : (∫ y in A, (ρ y)^2 ∂μ) ≤ ∫ y, (ρ y)^2 ∂μ :=
    setIntegral_le_integral hi (Eventually.of_forall fun y => sq_nonneg (ρ y))
  have hbound : m^2 / μ.real A ≤ ∫ y, (ρ y)^2 ∂μ := by
    apply (div_le_iff₀ hV).mpr
    exact (hsquare.trans hcs).trans (mul_le_mul_of_nonneg_right hglobal hV.le)
  rw [he, ← ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun y => sq_nonneg (ρ y))]
  exact ENNReal.ofReal_le_ofReal hbound

theorem heatOverlapKernel_short_diagonal_lower :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (q : X) (r : ℝ), 0 < r → -1 ≤ K*r^2 →
      ∀ (t : ℝ) (ht : 0 < t), t ≤ r^2 / (2*C) →
        ENNReal.ofReal ((1/4 : ℝ) / (hausdorff n X).real (closedBall q (2*r))) ≤
          hX.heatOverlapKernel hn p t ht q q := by
  obtain ⟨C, hC, hmass⟩ := hX.heatRadonMeasure_half_mass hn p
  refine ⟨C, hC, ?_⟩
  intro q r hr hcurv t ht htime
  have hfin := (hX.finiteOnBounded (closedBall q (2*r)) isBounded_closedBall).ne
  have hpos : 0 < (hausdorff n X) (closedBall q (2*r)) :=
    (hX.fullSupport q (2*r) (by positivity)).trans_le (measure_mono ball_subset_closedBall)
  have hV := ENNReal.toReal_pos hpos.ne' hfin
  have hh := hX.heatOverlapKernel_diagonal_lower_from_mass hn p t ht q hfin hV
    (by norm_num : (0 : ℝ) ≤ 1/2) (hmass q r hr hcurv t ht htime)
  norm_num only [show (1/2 : ℝ)^2 = 1/4 by norm_num] at hh
  exact hh

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
