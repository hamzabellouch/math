import OAI.GroupTheory.PolycyclicRecognition.Analysis.PairPathMesh

namespace OAI

/-! # Fixed-mesh sampling at large scale

A sublinear L² estimate on growing balls selects one actual pair with
small errors for most endpoints of a fixed finite family of sampled paths.
The finite mesh is chosen before the scale tends to infinity.
-/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace PolycyclicRecognition

/-- The finite-union Chebyshev bound can be made smaller than one half by
choosing a single positive L² tolerance, independently of scale. -/
theorem exists_mesh_tolerance (M : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ (M : ℝ≥0∞) *
      ((ENNReal.ofReal η)⁻¹ ^ 2 * ENNReal.ofReal δ ^ 2) < 1 / 2 := by
  have hη0 : ENNReal.ofReal η ≠ 0 := (ENNReal.ofReal_pos.mpr hη).ne'
  have hc : (M : ℝ≥0∞) * (ENNReal.ofReal η)⁻¹ ^ 2 ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top M)
      (ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr hη0))
  have ht : Filter.Tendsto (fun n : ℕ => (M : ℝ≥0∞) * (ENNReal.ofReal η)⁻¹ ^ 2 *
      ENNReal.ofReal (1 / ((n : ℝ) + 1)) ^ 2) Filter.atTop (nhds 0) := by
    have hp := ENNReal.Tendsto.pow (n := 2)
      (ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat)
    simpa using ENNReal.Tendsto.const_mul hp (Or.inr hc)
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1 / 2))).exists
  exact ⟨1 / ((n : ℝ) + 1), by positivity, by simpa [mul_assoc] using hn⟩

/-- For all sufficiently large scales there is a single normalized pair
whose normalized errors are small at every mesh point for more than half
the endpoints. No pointwise supremum over a path is used. -/
theorem eventually_exists_pair_good_on_mesh
    {G W I Y : Type*} [Group G] [MetricSpace G] [ProperSpace G]
    [IsTopologicalGroup G] [IsIsometricSMul G G] {Λ : ℝ≥0}
    [MeasurableSpace G] [BorelSpace G]
    [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
    [Fintype I] [MeasurableSpace Y]
    (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
    (ν : Measure Y) [IsProbabilityMeasure ν]
    (π l : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) (hl : Continuous fun g => (l g).toAdd)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g,
      ‖pairHeightL2 μ π hπ g - Lp.const 2 μ (l g).toAdd‖ ≤ ε * dist 1 g + B)
    (γ : ℝ → Y → I → G) (hγ : ∀ r i, Measurable (fun y => γ r y i))
    {R : ℝ} (hR : 0 ≤ R)
    (hball : ∀ r, 1 ≤ r → ∀ y i, dist 1 (γ r y i) ≤ R * r)
    {η : ℝ} (hη : 0 < η) :
    ∃ r₀ : ℝ, 1 ≤ r₀ ∧ ∀ r, r₀ ≤ r → ∃ p : NormalizedPair G Λ,
      ν {y | ∃ i, ENNReal.ofReal η ≤
        ‖r⁻¹ • (pairHeight π (γ r y i) p - (l (γ r y i)).toAdd)‖ₑ} < 1 / 2 := by
  obtain ⟨δ, hδ, hsmall⟩ := exists_mesh_tolerance (Fintype.card I) hη
  obtain ⟨r₁, _hr₁, hbound⟩ := uniform_sublinear_on_balls (fun g : G => dist 1 g) hsub hR δ hδ
  refine ⟨max 1 r₁, le_max_left _ _, fun r hr => ?_⟩
  have hr1 : 1 ≤ r := (le_max_left _ _).trans hr
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  let f : I → NormalizedPair G Λ × Y → W := fun i z =>
    r⁻¹ • (pairHeight π (γ r z.2 i) z.1 - (l (γ r z.2 i)).toAdd)
  have hf (i : I) : Measurable (f i) := by
    exact (((continuous_pairHeight π hπ).measurable.comp
      (((hγ r i).comp measurable_snd).prodMk measurable_fst)).sub
      (hl.measurable.comp ((hγ r i).comp measurable_snd))).const_smul _
  apply exists_good_mesh_fiber μ ν f hf
    (ENNReal.ofReal_pos.mpr hη).ne' ENNReal.ofReal_ne_top _ hsmall
  intro i y
  have hb := hbound r ((le_max_right _ _).trans hr) (γ r y i) (hball r hr1 y i)
  change eLpNorm (r⁻¹ • (fun p : NormalizedPair G Λ =>
    pairHeight π (γ r y i) p - (l (γ r y i)).toAdd)) 2 μ ≤ ENNReal.ofReal δ
  rw [eLpNorm_const_smul, eLpNorm_pairHeight_error μ π hπ l, ← ofReal_norm,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hrpos),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hrpos.le)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ r⁻¹ * (δ * r) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hrpos.le)
    _ = δ := by field_simp

end PolycyclicRecognition

end

end OAI
