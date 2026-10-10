import OAI.GroupTheory.PolycyclicRecognition.Analysis.StationarySampling
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CoarsePathMesh
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CoarsePathRadius

namespace OAI

/-! # Stationary sampling along controlled paths

A fixed finite mesh selects one normalized pair good for most independently
sampled endpoints. The coarse metric bound extends that mesh estimate to the
whole image path and retains the logarithmic error explicitly.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped NNReal ENNReal

variable {G W Y : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]
  [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  {Λ : ℝ≥0} [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  [MeasurableSpace Y]

/-- The finite-mesh bad set has mass less than one half; outside it every
point of the image path has controlled height. No supremum-in-`L²` is used. -/
theorem eventually_exists_pair_good_on_paths
    (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
    (ν : Measure Y) [IsProbabilityMeasure ν]
    (π l : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) (hl : Continuous fun g => (l g).toAdd)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g,
      ‖pairHeightL2 μ π hπ g - Lp.const 2 μ (l g).toAdd‖ ≤ ε * dist 1 g + B)
    {K C δ η : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (hδ : 0 < δ) (hη : 0 < η)
    (hLip : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y)
    (endpoint : ℝ → Y → G)
    (γ : ∀ r y, Path (1 : G) (endpoint r y))
    (hγ : ∀ r t, Measurable (fun y => γ r y t))
    (hpath : ∀ r, 1 ≤ r → ∀ y,
      PathMetricBound (γ r y) (C * r) (C * (1 + Real.log (2 + r))))
    (E : Set W)
    (hheight : ∀ r, 1 ≤ r → ∀ y t, ∃ w ∈ E, (l (γ r y t)).toAdd = r • w) :
    ∃ r₀ : ℝ, 1 ≤ r₀ ∧ ∀ r, r₀ ≤ r → ∃ (p : NormalizedPair G Λ) (B : Set Y),
      MeasurableSet B ∧ ν B < 1 / 2 ∧ ∀ y ∉ B, ∀ t,
        ∃ w ∈ E, ‖pairHeight π (γ r y t) p - r • w‖ ≤
          (K * Λ * C * δ + η) * r + K * Λ * C * (1 + Real.log (2 + r)) := by
  classical
  obtain ⟨S, hS⟩ := exists_fixed_path_mesh hδ
  let sample (r : ℝ) (y : Y) (i : S) := γ r y i.val
  obtain ⟨r₀, hr₀, hgood⟩ := eventually_exists_pair_good_on_mesh μ ν π l hπ hl hsub
    sample (fun r i => hγ r i.val) (by positivity : 0 ≤ 4 * C)
    (fun r hr y i => (hpath r hr y).dist_source_le_linear hC hr i.val) hη
  refine ⟨r₀, hr₀, ?_⟩
  intro r hr
  have hr1 : 1 ≤ r := hr₀.trans hr
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  obtain ⟨p, hp⟩ := hgood r hr
  let B : Set Y := {y | ∃ i : S, ENNReal.ofReal η ≤
    ‖r⁻¹ • (pairHeight π (sample r y i) p - (l (sample r y i)).toAdd)‖ₑ}
  have hB : MeasurableSet B := by
    dsimp only [B]
    simp only [ofPred_exists]
    apply MeasurableSet.iUnion
    intro i
    apply measurableSet_le measurable_const
    exact ((((continuous_pairHeight π hπ).measurable.comp
      ((hγ r i.val).prodMk measurable_const)).sub
      (hl.measurable.comp (hγ r i.val))).const_smul r⁻¹).enorm
  refine ⟨p, B, hB, hp, ?_⟩
  intro y hy
  have herr (u : unitInterval) (hu : u ∈ S) :
      ‖pairHeight π (γ r y u) p - (l (γ r y u)).toAdd‖ ≤ η * r := by
    have hn : ¬ ENNReal.ofReal η ≤
        ‖r⁻¹ • (pairHeight π (sample r y ⟨u, hu⟩) p -
          (l (sample r y ⟨u, hu⟩)).toAdd)‖ₑ := fun hh => hy ⟨⟨u, hu⟩, hh⟩
    have hlt := lt_of_not_ge hn
    rw [← ofReal_norm] at hlt
    have hh := (ENNReal.ofReal_lt_ofReal_iff hη).mp hlt
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hrpos)] at hh
    have hm := mul_le_mul_of_nonneg_left hh.le hrpos.le
    simpa only [sample, ← mul_assoc, mul_inv_cancel₀ hrpos.ne', one_mul, mul_comm r η] using hm
  have hcontrol := coarse_image_path_height_control (ε := 0) p π l hK hC hrpos.le hLip
    (γ r y) (fun t u => by
      simpa only [Subtype.dist_eq, Real.dist_eq] using hpath r hr1 y t u)
    S hS E (fun u _ => by
      obtain ⟨w, hw, he⟩ := hheight r hr1 y u
      exact ⟨w, hw, by simp [he]⟩) herr
  intro t
  obtain ⟨w, hw, hb⟩ := hcontrol t
  refine ⟨w, hw, ?_⟩
  convert hb using 1
  ring

end PolycyclicRecognition

end

end OAI
