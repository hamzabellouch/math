import OAI.GroupTheory.PolycyclicRecognition.Algebra.L2LabelDistance
import OAI.GroupTheory.PolycyclicRecognition.Analysis.PairMeasureScaling
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CocycleGrowth

namespace OAI

/-! # A fixed stationary slope gives increments close to the finite label set -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Metric Filter
open scoped NNReal ENNReal Topology

variable {G W : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] {Λ : ℝ≥0}
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]

omit [IsIsometricSMul G G] in
/-- Normalized increments inherit an L2 distance bound from any one label. -/
theorem lintegral_normalized_pair_label_distance_le
    (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
    (π : G →* Multiplicative W) (hπ : Continuous fun g => (π g).toAdd)
    (g : G) {r : ℝ} (hr : 0 < r) {S : Set W} {w : W} (hw : w ∈ S) :
    ∫⁻ p, ENNReal.ofReal (infDist (r⁻¹ • pairHeight π g p) S) ∂μ ≤
      ENNReal.ofReal (r⁻¹ * ‖pairHeightL2 μ π hπ g - Lp.const 2 μ (r • w)‖) := by
  let e := pairHeightL2 μ π hπ g - Lp.const 2 μ (r • w)
  let v := r⁻¹ • e
  have hae : (v : NormalizedPair G Λ → W) =ᵐ[μ]
      fun p => r⁻¹ • pairHeight π g p - w := by
    filter_upwards [Lp.coeFn_smul r⁻¹ e,
      Lp.coeFn_sub (pairHeightL2 μ π hπ g) (Lp.const 2 μ (r • w)),
      ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ (pairHeightProfile π hπ g),
      Lp.coeFn_const 2 μ (r • w)] with p hs he hp hc
    change pairHeightL2 μ π hπ g p = pairHeight π g p at hp
    rw [hs]
    change r⁻¹ • ((pairHeightL2 μ π hπ g - Lp.const 2 μ (r • w)) p) = _
    rw [he]
    simp only [Pi.sub_apply]
    rw [hp, hc]
    change r⁻¹ • (pairHeight π g p - r • w) = _
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  have h := lintegral_infDist_le_L2 μ _ v hw hae
  simpa only [v, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)] using h

omit [IsIsometricSMul G G] in
/-- The fixed-measure sublinear estimate implies convergence to the whole
label set along every linearly bounded family with the prescribed slope. -/
theorem normalized_pair_increments_tendsto_labels
    (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
    (π l : G →* Multiplicative W) (hπ : Continuous fun g => (π g).toAdd)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g,
      ‖pairHeightL2 μ π hπ g - Lp.const 2 μ (l g).toAdd‖ ≤ ε * dist 1 g + B)
    (g : ℝ → G) {R : ℝ} (hR : 0 ≤ R)
    (hsize : ∀ r, 1 ≤ r → dist 1 (g r) ≤ R * r)
    {S : Set W} {w : W} (hw : w ∈ S)
    (hslope : ∀ r, 1 ≤ r → (l (g r)).toAdd = r • w) :
    Tendsto (fun r : ℝ => ∫⁻ p,
      ENNReal.ofReal (infDist (r⁻¹ • pairHeight π (g r) p) S) ∂μ) atTop (𝓝 0) := by
  let e := fun x => pairHeightL2 μ π hπ x - Lp.const 2 μ (l x).toAdd
  have hlim : Tendsto (fun r : ℝ => r⁻¹ * ‖e (g r)‖) atTop (𝓝 0) := by
    apply tendsto_order.mpr
    constructor
    · intro a ha
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
      have hnonneg : 0 ≤ r⁻¹ * ‖e (g r)‖ := mul_nonneg (inv_nonneg.mpr (by linarith)) (norm_nonneg _)
      exact ha.trans_le hnonneg
    · intro ε hε
      obtain ⟨r₀, _, hb⟩ := uniform_sublinear_on_balls (fun x : G => dist 1 x) hsub hR
        (ε / 2) (half_pos hε)
      filter_upwards [eventually_ge_atTop (max 1 r₀)] with r hr
      have hr1 : 1 ≤ r := (le_max_left _ _).trans hr
      have hr0 : 0 < r := by linarith
      have h := mul_le_mul_of_nonneg_left
        (hb r ((le_max_right _ _).trans hr) (g r) (hsize r hr1)) (inv_nonneg.mpr hr0.le)
      have he : r⁻¹ * ‖e (g r)‖ ≤ ε / 2 := by
        simpa only [e, ← mul_assoc, mul_left_comm r⁻¹, inv_mul_cancel₀ hr0.ne', mul_one] using h
      linarith
  have hupper : Tendsto (fun r : ℝ => ENNReal.ofReal (r⁻¹ * ‖e (g r)‖)) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Eventually.of_forall (fun _ => zero_le))
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  have hb := lintegral_normalized_pair_label_distance_le μ π hπ (g r)
    (by linarith : 0 < r) hw
  simpa only [e, hslope r hr] using hb

end PolycyclicRecognition

end

end OAI
