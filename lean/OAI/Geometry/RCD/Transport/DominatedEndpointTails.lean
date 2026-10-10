import OAI.Geometry.RCD.Transport.GeodesicPlanTightness

namespace OAI

/-! # Uniform endpoint tails from domination by fixed probability measures -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SeparableSpace X] [ProperSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem finite_measure_closedBall_tail
    (μ : Measure X) [IsFiniteMeasure μ] (p : X) {ε : ℝ≥0∞} (hε : 0<ε) :
    ∃ R : ℝ, 0≤R ∧ μ {x | R<dist x p}≤ε := by
  have ht : Tendsto (fun r : ℝ => μ (closedBall p r)ᶜ) atTop (𝓝 0) := by
    simpa only [Set.mem_singleton_iff,iSup_iSup_eq_left] using
      tendsto_measure_compl_closedBall_of_isTightMeasureSet
        (isTightMeasureSet_singleton (μ:=μ)) p
  obtain ⟨R,hR⟩ := ENNReal.tendsto_atTop_zero.mp ht ε hε
  refine ⟨max R 0,le_max_right _ _,?_⟩
  have he : {x : X | max R 0<dist x p}=(closedBall p (max R 0))ᶜ := by
    ext x
    simp only [mem_compl_iff,mem_closedBall,not_le,mem_ofPred_eq]
  rw [he]
  exact hR (max R 0) (le_max_left _ _)

theorem dominated_endpoint_tails
    (πs : ℕ → ProbabilityMeasure C(Time,X)) (ν₀ ν₁ : ProbabilityMeasure X) (p : X)
    (h0 : ∀ j, (πs j : Measure C(Time,X)).map (fun γ => γ 0)≤(2 : ℝ≥0∞) • (ν₀ : Measure X))
    (h1 : ∀ j, (πs j : Measure C(Time,X)).map (fun γ => γ 1)≤(2 : ℝ≥0∞) • (ν₁ : Measure X)) :
    ∀ ε : ℝ≥0∞, 0<ε → ∃ R : ℝ, 0≤R ∧ ∀ j,
      (πs j : Measure C(Time,X)) {γ | R<dist (γ 0) p}+
      (πs j : Measure C(Time,X)) {γ | R<dist (γ 1) p}≤ε := by
  let μ := (2 : ℝ≥0∞) • (ν₀ : Measure X)+(2 : ℝ≥0∞) • (ν₁ : Measure X)
  let : IsFiniteMeasure μ := ⟨by
    change (2 : ℝ≥0∞)*(ν₀ : Measure X) univ+2*(ν₁ : Measure X) univ<∞
    simp⟩
  intro ε hε
  obtain ⟨R,hR,hRμ⟩ := finite_measure_closedBall_tail μ p hε
  refine ⟨R,hR,fun j => ?_⟩
  have hB : MeasurableSet {x : X | R<dist x p} :=
    (isOpen_lt continuous_const (continuous_id.dist continuous_const)).measurableSet
  have he (t : Time) :
      (πs j : Measure C(Time,X)) {γ | R<dist (γ t) p}=
        ((πs j : Measure C(Time,X)).map (fun γ => γ t)) {x | R<dist x p} :=
    (Measure.map_apply (measurable_path_eval t) hB).symm
  rw [he 0,he 1]
  exact (add_le_add (h0 j _) (h1 j _)).trans hRμ

end RegularPointCoordinates

end

end OAI
