import OAI.GroupTheory.PolycyclicRecognition.Analysis.HaarAveragingScales
import OAI.GroupTheory.PolycyclicRecognition.Analysis.NilpotentBallVolume
import OAI.GroupTheory.PolycyclicRecognition.Analysis.NilpotentHaarSymmetry
import OAI.GroupTheory.PolycyclicRecognition.Geometry.BoundaryHeight

namespace OAI

/-! # Boundary trace comparison on actual nilpotent groups

This proves the averaging step from the explicit published exponential inputs
and the already chosen proper chain metric. No doubling premise is retained.
-/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory MeasureTheory.Measure Metric
open scoped Manifold ENNReal NNReal

variable {G E J P : Type*} [Group G] [MetricSpace G] [IsIsometricSMul G G]
  [ProperSpace G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [ChartedSpace E G] [LieGroup (𝓘(ℝ, E)) ⊤ G] [SimplyConnectedSpace G]

/-- Uniform translated boundary masses determine their exponential volume
characters, with a bound independent of the compact sets' diameters. -/
theorem trace_bound_of_nilpotent_boundary_masses
    (chains : LinearMetricChains G)
    (dynkin : NilpotentDynkinExpansionInput E G)
    (haar : NilpotentExponentialHaarInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) G))
    (μ : Measure G) (ρ : P → Measure G) [μ.IsHaarMeasure] [∀ p, SFinite (ρ p)]
    (sets : J → Set G) (source : J → ℝ) (target : P → J → ℝ)
    (hsets : ∀ j, IsCompact (sets j)) {c K : ℝ} (hc : 0 < c) (hK : 0 < K)
    (hvolume : ∀ j, μ (sets j) = ENNReal.ofReal (c * Real.exp (source j)))
    (hlower : ∀ p j z, ENNReal.ofReal (Real.exp (target p j)) ≤
      ENNReal.ofReal K * ρ p (leftTranslate (sets j) z))
    (hupper : ∀ p j z, ρ p (leftTranslate (sets j) z) ≤
      ENNReal.ofReal K * ENNReal.ofReal (Real.exp (target p j))) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p j j₀,
      |(target p j - target p j₀) - (source j - source j₀)| ≤ B := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  let : μ.IsInvInvariant := nilpotent_haar_isInvInvariant haar Exp hExp hnil μ
  let : μ.IsMulRightInvariant := nilpotent_haar_isMulRightInvariant haar Exp hExp hnil μ
  obtain ⟨C, _, d, hvol⟩ := haar_polynomial_ball_volume chains dynkin haar Exp hExp hnil μ
  let D : ℝ := 2 * (3 : ℝ) ^ d
  have hD : 0 < D := by dsimp [D]; positivity
  have hcmp (p : P) := haar_averaging_compact_of_polynomial_volume μ (ρ p) sets
    (fun j => ENNReal.ofReal (Real.exp (target p j))) hsets ENNReal.ofReal_ne_top
    (hlower p) (hupper p) (fun R hR =>
      ⟨(measure_ball_pos μ 1 (by linarith : 0 < R)).ne', measure_ball_ne_top⟩) d hvol
  have hreal (p : P) (j k : J) :
      Real.exp (target p j) * Real.exp (source k) ≤
        (K * K * D) * (Real.exp (target p k) * Real.exp (source j)) := by
    have h := hcmp p j k
    rw [hvolume j, hvolume k] at h
    change ENNReal.ofReal (Real.exp (target p j)) *
        ENNReal.ofReal (c * Real.exp (source k)) ≤
      (ENNReal.ofReal K * ENNReal.ofReal K * ENNReal.ofReal D) *
        ENNReal.ofReal (Real.exp (target p k)) *
        ENNReal.ofReal (c * Real.exp (source j)) at h
    have h' := ENNReal.toReal_mono (by finiteness) h
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le,
      ENNReal.toReal_ofReal hK.le, ENNReal.toReal_ofReal hD.le,
      ENNReal.toReal_ofReal (mul_pos hc (Real.exp_pos _)).le] at h'
    apply (mul_le_mul_iff_right₀ hc).mp
    convert h' using 1 <;> ring
  refine ⟨max 0 (Real.log (K * K * D)), le_max_left _ _, ?_⟩
  intro p j j₀
  have h := abs_log_sub_le_of_comparison
    (mul_pos (Real.exp_pos (target p j)) (Real.exp_pos (source j₀)))
    (mul_pos (Real.exp_pos (target p j₀)) (Real.exp_pos (source j)))
    (by positivity : 0 < K * K * D) (hreal p j j₀) (hreal p j₀ j)
  simp only [Real.log_mul (Real.exp_ne_zero _) (Real.exp_ne_zero _), Real.log_exp] at h
  apply (show |(target p j - target p j₀) - (source j - source j₀)| ≤
      Real.log (K * K * D) from ?_).trans (le_max_right _ _)
  convert h using 1
  congr 1
  ring

end PolycyclicRecognition

end

end OAI
