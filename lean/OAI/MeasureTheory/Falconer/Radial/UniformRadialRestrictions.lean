import OAI.MeasureTheory.Falconer.Angular.CircleTests
import OAI.MeasureTheory.Falconer.Frostman.AtomlessRadialContinuity
import OAI.MeasureTheory.Falconer.Geometry.CompactSublevel

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
open scoped ENNReal NNReal

theorem radial_densityNorm_normalized_restrict_le (ν : ProbabilityMeasure Plane)
    (B : Set Plane) (hB : 0 < (ν : Measure Plane) B)
    (ν' : ProbabilityMeasure Plane)
    (hν' : (ν' : Measure Plane) = ((ν : Measure Plane) B)⁻¹ • (ν : Measure Plane).restrict B)
    {p q : ℝ} (hpq : p.HolderConjugate q) (x : Plane) :
    sourceDensityNorm p ((ν' : Measure Plane).map (sourceRadialUnit x)) ≤
      ((ν : Measure Plane) B)⁻¹ * sourceDensityNorm p ((ν : Measure Plane).map (sourceRadialUnit x)) := by
  simp_rw [← sourceTestNorm_eq_densityNorm _ hpq]
  rw [hν', Measure.map_smul _ (measurable_sourceRadialUnit x).aemeasurable]
  exact (sourceTestNorm_smul_le _ _ (ENNReal.inv_ne_top.mpr hB.ne') q).trans
    (mul_le_mul_right (sourceTestNorm_mono _ _
      (Measure.map_mono Measure.restrict_le_self (measurable_sourceRadialUnit x)) q) _)

theorem uniform_restrictions_of_finite_radial_moments
    (μ₀ ν₀ : ProbabilityMeasure Plane)
    (hμK : IsCompact (μ₀ : Measure Plane).support)
    (hνK : IsCompact (ν₀ : Measure Plane).support)
    {s C p q : ℝ} (hs : 0 < s) (hC : 0 < C)
    (hμball : BallBound μ₀ s C) (hνball : BallBound ν₀ s C)
    (hpq : p.HolderConjugate q)
    (hIμ : (∫⁻ x, (sourceDensityNorm p ((ν₀ : Measure Plane).map (sourceRadialUnit x)))^p ∂μ₀) < ∞)
    (hIν : (∫⁻ x, (sourceDensityNorm p ((μ₀ : Measure Plane).map (sourceRadialUnit x)))^p ∂ν₀) < ∞) :
    ∃ μ ν : ProbabilityMeasure Plane,
      IsCompact (μ : Measure Plane).support ∧ IsCompact (ν : Measure Plane).support ∧
      (μ : Measure Plane).support ⊆ (μ₀ : Measure Plane).support ∧
      (ν : Measure Plane).support ⊆ (ν₀ : Measure Plane).support ∧
      ∃ D : ℝ, 0 < D ∧ BallBound μ s D ∧ BallBound ν s D ∧
      ∃ K : ℝ≥0∞, K ≠ ∞ ∧
        (∀ x ∈ (μ : Measure Plane).support,
          sourceDensityNorm p ((ν : Measure Plane).map (sourceRadialUnit x)) ≤ K) ∧
        (∀ y ∈ (ν : Measure Plane).support,
          sourceDensityNorm p ((μ : Measure Plane).map (sourceRadialUnit y)) ≤ K) := by
  let := noAtoms_of_ball_bound μ₀ hs hμball
  let := noAtoms_of_ball_bound ν₀ hs hνball
  obtain ⟨A, hA, hAμ, hAp, KA, hKA, hAb⟩ := exists_positive_compact_sublevel
    (μ₀ : Measure Plane) hμK (μ₀ : Measure Plane).support_mem_ae
    (fun x => sourceDensityNorm p ((ν₀ : Measure Plane).map (sourceRadialUnit x)))
    (sourceDensityNorm_atomless_radial_lowerSemicontinuous ν₀ hpq) hpq.pos hIμ
  obtain ⟨B, hB, hBν, hBp, KB, hKB, hBb⟩ := exists_positive_compact_sublevel
    (ν₀ : Measure Plane) hνK (ν₀ : Measure Plane).support_mem_ae
    (fun x => sourceDensityNorm p ((μ₀ : Measure Plane).map (sourceRadialUnit x)))
    (sourceDensityNorm_atomless_radial_lowerSemicontinuous μ₀ hpq) hpq.pos hIν
  obtain ⟨μ, hμA, Dμ, hDμ, hbμ, heμ⟩ := normalized_restriction_ball_bound μ₀ hμball hC A hA.measurableSet hAp
  obtain ⟨ν, hνB, Dν, hDν, hbν, heν⟩ := normalized_restriction_ball_bound ν₀ hνball hC B hB.measurableSet hBp
  have hμsub := support_subset_carrier μ hA.isClosed hμA
  have hνsub := support_subset_carrier ν hB.isClosed hνB
  have heμ' : (μ : Measure Plane) = ((μ₀ : Measure Plane) A)⁻¹ • (μ₀ : Measure Plane).restrict A := by
    simpa only [ENNReal.ofReal_toReal (measure_ne_top _ _)] using heμ
  have heν' : (ν : Measure Plane) = ((ν₀ : Measure Plane) B)⁻¹ • (ν₀ : Measure Plane).restrict B := by
    simpa only [ENNReal.ofReal_toReal (measure_ne_top _ _)] using heν
  let K := max (((ν₀ : Measure Plane) B)⁻¹ * KA) (((μ₀ : Measure Plane) A)⁻¹ * KB)
  refine ⟨μ, ν, hA.of_isClosed_subset Measure.isClosed_support hμsub,
    hB.of_isClosed_subset Measure.isClosed_support hνsub, hμsub.trans hAμ, hνsub.trans hBν,
    max Dμ Dν, hDμ.trans_le (le_max_left _ _), ?_, ?_, K, ?_, ?_, ?_⟩
  · intro x r hr
    exact (hbμ x r hr).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
  · intro x r hr
    exact (hbν x r hr).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))
  · exact ne_of_lt (max_lt (ENNReal.mul_lt_top (ENNReal.inv_ne_top.mpr hBp.ne').lt_top hKA.lt_top)
      (ENNReal.mul_lt_top (ENNReal.inv_ne_top.mpr hAp.ne').lt_top hKB.lt_top))
  · intro x hx
    exact (radial_densityNorm_normalized_restrict_le ν₀ B hBp ν heν' hpq x).trans
      ((mul_le_mul_right (hAb x (hμsub hx)) _).trans (le_max_left _ _))
  · intro y hy
    exact (radial_densityNorm_normalized_restrict_le μ₀ A hAp μ heμ' hpq y).trans
      ((mul_le_mul_right (hBb y (hνsub hy)) _).trans (le_max_right _ _))

end PlanarFalconer

end OAI
