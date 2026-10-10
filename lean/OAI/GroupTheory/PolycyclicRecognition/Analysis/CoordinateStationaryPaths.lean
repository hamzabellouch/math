import OAI.GroupTheory.PolycyclicRecognition.Analysis.StationaryPathSampling
import OAI.GroupTheory.PolycyclicRecognition.Analysis.NormalizedEndpointMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

namespace OAI

/-! # Independent coordinate sampling for nonnegative path families

This bridge normalizes coordinate volume once and extends a family from
nonnegative scales. It separates finite-measure sampling from the Lie
coordinate constructions that supply the paths.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Metric Set
open scoped NNReal ENNReal

variable {G W : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  {Λ : ℝ≥0} [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]

/-- Continuous coding on a common coordinate ball supplies a good endpoint
set of at least half its volume at every sufficiently large scale. -/
theorem coordinate_stationary_paths {n : ℕ} {ε C K : ℝ} (hε : 0 < ε) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
    (π l : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) (hl : Continuous fun g => (l g).toAdd)
    (hLip : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y)
    (hsub : ∀ η : ℝ, 0 < η → ∃ B : ℝ, 0 ≤ B ∧ ∀ g,
      ‖pairHeightL2 μ π hπ g - Lp.const 2 μ (l g).toAdd‖ ≤ η * dist 1 g + B)
    (E : Set W)
    (endpoint : ℝ → ball (0 : Fin n → ℝ) ε → G)
    (hcode : ∀ r : ℝ, 0 ≤ r → ∃ γ : ∀ y, Path (1 : G) (endpoint r y),
      (∀ t, Continuous (fun y => γ y t)) ∧
      (∀ y, PathMetricBound (γ y) (C * r) (C * (1 + Real.log (2 + r)))) ∧
      ∀ y t, ∃ w ∈ E, (l (γ y t)).toAdd = r • w) :
    ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η → ∃ r₀ : ℝ, 1 ≤ r₀ ∧
      ∀ r : ℝ, r₀ ≤ r → ∃ (p : NormalizedPair G Λ) (B : Set (ball (0 : Fin n → ℝ) ε)),
        MeasurableSet B ∧ volume (ball (0 : Fin n → ℝ) ε) * (1 / 2) ≤ volume (Subtype.val '' Bᶜ) ∧
        ∀ y ∉ B, ∃ γ : Path (1 : G) (endpoint r y),
          PathMetricBound γ (C * r) (C * (1 + Real.log (2 + r))) ∧
          ∀ t, ∃ w ∈ E, ‖pairHeight π (γ t) p - r • w‖ ≤
            (K * Λ * C * δ + η) * r + K * Λ * C * (1 + Real.log (2 + r)) := by
  classical
  let V := Fin n → ℝ
  let S := ball (0 : V) ε
  let Y := S
  have hS : MeasurableSet S := measurableSet_ball
  have hS₀ : volume S ≠ 0 := (measure_ball_pos volume (0 : V) hε).ne'
  have hSfin : volume S ≠ ⊤ := ne_of_lt <|
    lt_of_le_of_lt (measure_mono ball_subset_closedBall) (isCompact_closedBall (0 : V) ε).measure_lt_top
  let ν := normalizedEndpointMeasure volume S
  let : IsProbabilityMeasure ν := normalizedEndpointMeasure_isProbability volume hS hS₀ hSfin
  choose γ hγ hb hh using (fun r : ℝ => hcode (max 0 r) (le_max_left _ _))
  intro δ hδ η hη
  obtain ⟨r₀, hr₀, hgood⟩ := eventually_exists_pair_good_on_paths μ ν π l hπ hl hsub
    hK hC hδ hη hLip (fun r => endpoint (max 0 r)) γ (fun r t => (hγ r t).measurable)
    (fun r hr y => by simpa only [max_eq_right (by linarith : 0 ≤ r)] using hb r y)
    E (fun r hr y t => by simpa only [max_eq_right (by linarith : 0 ≤ r)] using hh r y t)
  refine ⟨r₀, hr₀, ?_⟩
  intro r hr
  obtain ⟨p, B, hB, hmass, hheight⟩ := hgood r hr
  refine ⟨p, B, hB, half_volume_le_good_endpoints volume hS hS₀ hSfin hB hmass, ?_⟩
  intro y hy
  have he : max 0 r = r := max_eq_right (by linarith [hr₀.trans hr])
  refine ⟨(γ r y).cast rfl (by rw [he]), ?_, hheight y hy⟩
  have hm : PathMetricBound (γ r y) (C * r) (C * (1 + Real.log (2 + r))) := by
    simpa only [he] using hb r y
  exact hm.cast rfl (by rw [he])

end PolycyclicRecognition

end

end OAI
