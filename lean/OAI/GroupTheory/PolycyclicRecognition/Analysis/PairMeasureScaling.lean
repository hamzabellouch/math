import OAI.GroupTheory.PolycyclicRecognition.Analysis.PairPathMesh

namespace OAI

/-! # Normalizing a finite stationary measure

The inverse coupling produces a finite nonzero measure. Its probability
normalization retains the same sublinear error and therefore the same
prescribed inverse coefficient.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped NNReal ENNReal

variable {G W : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] {Λ : ℝ≥0}
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

omit [IsIsometricSMul G G] in
/-- The pointwise error and the Hilbert error agree for every finite measure. -/
theorem eLpNorm_pairHeight_error_finite
    (μ : Measure (NormalizedPair G Λ)) [IsFiniteMeasure μ]
    (π : G →* Multiplicative W) (hπ : Continuous fun g => (π g).toAdd)
    (l : G →* Multiplicative W) (g : G) :
    eLpNorm (fun p : NormalizedPair G Λ => pairHeight π g p - (l g).toAdd) 2 μ =
      ENNReal.ofReal ‖pairHeightL2 μ π hπ g - Lp.const 2 μ (l g).toAdd‖ := by
  rw [ofReal_norm, Lp.enorm_def]
  apply eLpNorm_congr_ae
  exact ((ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ (pairHeightProfile π hπ g)).sub
    (Lp.coeFn_const 2 μ (l g).toAdd)).symm.trans (Lp.coeFn_sub _ _).symm

omit [IsIsometricSMul G G] in
/-- Scaling the measure scales every height-error norm by one fixed factor. -/
theorem norm_pairHeight_error_smul_measure
    (μ : Measure (NormalizedPair G Λ)) [IsFiniteMeasure μ]
    (c : ℝ≥0∞) [IsFiniteMeasure (c • μ)]
    (π : G →* Multiplicative W) (hπ : Continuous fun g => (π g).toAdd)
    (l : G →* Multiplicative W) (g : G) :
    ‖pairHeightL2 (c • μ) π hπ g - Lp.const 2 (c • μ) (l g).toAdd‖ =
      (c ^ (1 / 2 : ℝ)).toReal * ‖pairHeightL2 μ π hπ g - Lp.const 2 μ (l g).toAdd‖ := by
  have h := eLpNorm_smul_measure_of_ne_zero_of_ne_top
    (μ := μ) (f := fun p : NormalizedPair G Λ => pairHeight π g p - (l g).toAdd)
    (p := 2) (by norm_num) (by norm_num) c
  rw [eLpNorm_pairHeight_error_finite, eLpNorm_pairHeight_error_finite] at h
  have hr := congrArg ENNReal.toReal h
  simpa only [ENNReal.toReal_ofReal (norm_nonneg _), smul_eq_mul,
    ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] using hr

omit [IsIsometricSMul G G] in
/-- Sublinearity survives every finite scaling of the stationary measure. -/
theorem pairHeight_sublinear_smul_measure
    (μ : Measure (NormalizedPair G Λ)) [IsFiniteMeasure μ]
    (c : ℝ≥0∞) [IsFiniteMeasure (c • μ)]
    (π l : G →* Multiplicative W) (hπ : Continuous fun g => (π g).toAdd)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g,
      ‖pairHeightL2 μ π hπ g - Lp.const 2 μ (l g).toAdd‖ ≤ ε * dist 1 g + B) :
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g,
      ‖pairHeightL2 (c • μ) π hπ g - Lp.const 2 (c • μ) (l g).toAdd‖ ≤
        ε * dist 1 g + B := by
  intro ε hε
  let C := (c ^ (1 / 2 : ℝ)).toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  obtain ⟨B, hB, hb⟩ := hsub (ε / (C + 1)) (div_pos hε (by positivity))
  refine ⟨C * B, mul_nonneg hC hB, fun g => ?_⟩
  rw [norm_pairHeight_error_smul_measure]
  have hh := mul_le_mul_of_nonneg_left (hb g) hC
  have hc : C * (ε / (C + 1)) ≤ ε := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  calc
    _ ≤ C * (ε / (C + 1) * dist 1 g + B) := hh
    _ = C * (ε / (C + 1)) * dist 1 g + C * B := by ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hc dist_nonneg) le_rfl

/-- A finite nonzero invariant measure can be normalized without changing
its prescribed sublinear slope. -/
theorem exists_probability_with_same_pairHeight_slope
    (μ : Measure (NormalizedPair G Λ)) [IsFiniteMeasure μ]
    [SMulInvariantMeasure G (NormalizedPair G Λ) μ] (hμ : μ ≠ 0)
    (π l : G →* Multiplicative W) (hπ : Continuous fun g => (π g).toAdd)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g,
      ‖pairHeightL2 μ π hπ g - Lp.const 2 μ (l g).toAdd‖ ≤ ε * dist 1 g + B) :
    ∃ ν : Measure (NormalizedPair G Λ), ∃ hν : IsProbabilityMeasure ν,
      SMulInvariantMeasure G (NormalizedPair G Λ) ν ∧
      let := hν
      ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g,
        ‖pairHeightL2 ν π hπ g - Lp.const 2 ν (l g).toAdd‖ ≤ ε * dist 1 g + B := by
  have hmass : μ univ ≠ 0 := fun h => hμ (Measure.measure_univ_eq_zero.mp h)
  let ν := (μ univ)⁻¹ • μ
  have hν : IsProbabilityMeasure ν := by
    constructor
    change ((μ univ)⁻¹ • μ) univ = 1
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hmass (measure_lt_top μ univ).ne
  let := hν
  refine ⟨ν, hν, inferInstance, ?_⟩
  exact pairHeight_sublinear_smul_measure μ (μ univ)⁻¹ π l hπ hsub

end PolycyclicRecognition

end

end OAI
