import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialTripling
import OAI.GroupTheory.PolycyclicRecognition.Analysis.NilpotentBallVolume
import Mathlib.MeasureTheory.Measure.Haar.Basic

namespace OAI

/-! # Good closed-ball scales for nilpotent Haar measure

Polynomial upper growth alone supplies a sequence of compact balls tending
to infinity with bounded tripling ratio. No lower growth asymptotic is used.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory MeasureTheory.Measure Metric Filter
open scoped Manifold Topology

variable {G : Type*} [Group G] [MetricSpace G] [IsTopologicalGroup G]
  [ProperSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]

omit [IsTopologicalGroup G] [BorelSpace G] in
theorem closedBall_measureReal_pos {r : ℝ} (hr : 0 < r) :
    0 < μ.real (closedBall (1 : G) r) := by
  apply ENNReal.toReal_pos
  · exact (ne_of_gt (lt_of_lt_of_le (measure_ball_pos μ 1 hr)
      (measure_mono ball_subset_closedBall)))
  · exact (isCompact_closedBall 1 r).measure_ne_top

omit [IsTopologicalGroup G] [BorelSpace G] in
/-- Convert the open-ball polynomial estimate to closed balls. -/
theorem closedBall_polynomial_bound {C : ℝ} {d : ℕ}
    (h : ∀ r : ℝ, 1 ≤ r → μ.real (ball 1 r) ≤ C * r ^ d) :
    ∀ r : ℝ, 1 ≤ r → μ.real (closedBall 1 r) ≤ (C * 2 ^ d) * r ^ d := by
  intro r hr
  have hsub : closedBall (1 : G) r ⊆ ball 1 (2 * r) := by
    apply closedBall_subset_ball
    linarith
  have hle := ENNReal.toReal_mono (measure_ball_ne_top (μ := μ) (x := (1 : G))
    (r := 2 * r)) (measure_mono hsub)
  exact hle.trans ((h (2 * r) (by linarith)).trans_eq (by rw [mul_pow]; ring))

omit [IsTopologicalGroup G] [BorelSpace G] in
/-- Choose good radii cofinally, retaining the exact closed-ball ratio. -/
theorem exists_closedBall_tripling_scales {C : ℝ} {d : ℕ}
    (h : ∀ r : ℝ, 1 ≤ r → μ.real (ball 1 r) ≤ C * r ^ d) :
    ∃ scale : ℕ → ℝ,
      (∀ n, 1 ≤ scale n) ∧ Tendsto scale atTop atTop ∧
      ∀ n, μ.real (closedBall 1 (3 * scale n)) ≤
        (2 * (3 : ℝ) ^ d) * μ.real (closedBall 1 (scale n)) := by
  have hb := closedBall_polynomial_bound μ h
  have hg := polynomial_tripling_at_arbitrarily_large_radii
    (fun r => μ.real (closedBall 1 r)) d
    (fun r hr => closedBall_measureReal_pos μ (by linarith)) hb
  choose scale hlarge hone hratio using fun n : ℕ => hg (n : ℝ)
  refine ⟨scale, hone, ?_, hratio⟩
  exact tendsto_atTop_mono hlarge tendsto_natCast_atTop_atTop

omit [IsTopologicalGroup G] [BorelSpace G] in
/-- The good radii may all be chosen above any fixed lower threshold. -/
theorem exists_closedBall_tripling_scales_above {C : ℝ} {d : ℕ}
    (h : ∀ r : ℝ, 1 ≤ r → μ.real (ball 1 r) ≤ C * r ^ d) (R : ℝ) :
    ∃ scale : ℕ → ℝ,
      (∀ n, max R 1 ≤ scale n) ∧ Tendsto scale atTop atTop ∧
      ∀ n, μ.real (closedBall 1 (3 * scale n)) ≤
        (2 * (3 : ℝ) ^ d) * μ.real (closedBall 1 (scale n)) := by
  have hb := closedBall_polynomial_bound μ h
  have hg := polynomial_tripling_at_arbitrarily_large_radii
    (fun r => μ.real (closedBall 1 r)) d
    (fun r hr => closedBall_measureReal_pos μ (by linarith)) hb
  choose scale hlarge hone hratio using fun n : ℕ => hg ((n : ℝ) + max R 1)
  refine ⟨scale, fun n => ?_, ?_, hratio⟩
  · exact (le_add_of_nonneg_left (Nat.cast_nonneg n)).trans (hlarge n)
  · apply tendsto_atTop_mono _ tendsto_natCast_atTop_atTop
    intro n
    exact (le_add_of_nonneg_right (by positivity : 0 ≤ max R 1)).trans (hlarge n)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [ChartedSpace E G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [SimplyConnectedSpace G] [SecondCountableTopology G] [IsIsometricSMul G G]

omit [IsTopologicalGroup G] in
/-- The nilpotent Dynkin and Haar constructions provide all growth inputs
for the good scales used in the Cartan semidirect cover. -/
theorem nilpotent_closedBall_tripling_scales
    (chains : LinearMetricChains G) (dynkin : NilpotentDynkinExpansionInput E G)
    (haar : NilpotentExponentialHaarInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) G)) :
    ∃ (scale : ℕ → ℝ) (D : ℝ), (∀ n, 1 ≤ scale n) ∧
      Tendsto scale atTop atTop ∧ 0 ≤ D ∧
      ∀ n, μ.real (closedBall 1 (3 * scale n)) ≤ D * μ.real (closedBall 1 (scale n)) := by
  obtain ⟨C, _, d, hC⟩ := haar_polynomial_ball_volume chains dynkin haar Exp hExp hnil μ
  obtain ⟨scale, hscale, hlim, hratio⟩ := exists_closedBall_tripling_scales μ hC
  exact ⟨scale, 2 * 3 ^ d, hscale, hlim, by positivity, hratio⟩

omit [IsTopologicalGroup G] in
theorem nilpotent_closedBall_tripling_scales_above
    (chains : LinearMetricChains G) (dynkin : NilpotentDynkinExpansionInput E G)
    (haar : NilpotentExponentialHaarInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) G)) (R : ℝ) :
    ∃ (scale : ℕ → ℝ) (D : ℝ), (∀ n, max R 1 ≤ scale n) ∧
      Tendsto scale atTop atTop ∧ 0 ≤ D ∧
      ∀ n, μ.real (closedBall 1 (3 * scale n)) ≤ D * μ.real (closedBall 1 (scale n)) := by
  obtain ⟨C, _, d, hC⟩ := haar_polynomial_ball_volume chains dynkin haar Exp hExp hnil μ
  obtain ⟨scale, hscale, hlim, hratio⟩ := exists_closedBall_tripling_scales_above μ hC R
  exact ⟨scale, 2 * 3 ^ d, hscale, hlim, by positivity, hratio⟩

end PolycyclicRecognition

end

end OAI
