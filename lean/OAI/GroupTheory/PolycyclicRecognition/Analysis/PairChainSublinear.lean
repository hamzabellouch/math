import OAI.GroupTheory.PolycyclicRecognition.Analysis.MetricChainWords
import OAI.GroupTheory.PolycyclicRecognition.Analysis.PairSublinear

namespace OAI

/-! # Transfer sublinearity using only large-scale metric chains -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Metric
open scoped NNReal

attribute [local instance] stationaryL2Action

variable {G W : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] {Λ : ℝ≥0}
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The compact-uniform transfer estimate gives sublinearity for the
compatible metric selected by the published metric-existence input. -/
theorem pairHeight_sublinear_of_linearChains
    (μ : Measure (NormalizedPair G Λ)) [IsFiniteMeasure μ]
    [SMulInvariantMeasure G (NormalizedPair G Λ) μ]
    (C : LinearMetricChains G)
    (π l : G →* Multiplicative W) (hπ : Continuous fun g => (π g).toAdd)
    (φ : ℕ → NormalizedPair G Λ → W) (hφ : ∀ n, MemLp (φ n) 2 μ)
    (happrox : ∀ Q : Set G, IsCompact Q →
      Filter.Tendsto (fun n => ⨆ t ∈ Q,
        ∫⁻ p, ‖pairTransferDefect π l (φ n) t p‖ₑ ^ 2 ∂μ) Filter.atTop (nhds 0)) :
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g,
      ‖pairHeightL2 μ π hπ g - Lp.const 2 μ (l g).toAdd‖ ≤ ε * dist 1 g + B := by
  apply pairHeight_sublinear_of_squared_errors μ π l hπ φ hφ
    (closedBall 1 C.step) (fun g => dist 1 g) (fun _ => dist_nonneg)
    (a := C.slope + C.error) (add_nonneg C.slope_nonneg C.error_nonneg)
  · intro g
    obtain ⟨w, hw, hprod, hlen⟩ := C.wordFactorization g
    refine ⟨w, hw, hprod, hlen.trans ?_⟩
    nlinarith [mul_nonneg C.error_nonneg (dist_nonneg (x := (1 : G)) (y := g)),
      C.slope_nonneg]
  · exact happrox _ (isCompact_closedBall 1 C.step)

/-- The actual inverse coupling supplies a sublinear inverse height error
with exactly the inverse coefficient. No ergodicity of its finite measure
and no second reduced-cohomology hypothesis are required. The metric
assumption is precisely the published large-scale chain condition. -/
theorem inverseCoupling_sublinear_of_linearChains
    {G W : Type*} [Group G] [MetricSpace G] [ProperSpace G]
    [SecondCountableTopology G] [IsTopologicalGroup G] [IsIsometricSMul G G]
    {Λ : ℝ≥0} [MeasurableSpace G] [BorelSpace G]
    [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [SecondCountableTopology W]
    [MeasurableSpace W] [BorelSpace W]
    (m : Measure G) [m.IsHaarMeasure] [m.IsMulRightInvariant]
    (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
    [SMulInvariantMeasure G (NormalizedPair G Λ) μ]
    (A : W ≃L[ℝ] W) (π l : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) (hl : Continuous fun g => (l g).toAdd)
    (hlA : ∀ g, (l g).toAdd = A (π g).toAdd)
    (φ : ℕ → NormalizedPair G Λ → W)
    (hφ : ∀ n, MemLp (φ n) 2 μ) (hφm : ∀ n, Measurable (φ n))
    (happrox : ∀ T : Set G, IsCompact T →
      Filter.Tendsto (fun n => ⨆ t ∈ T,
        ∫⁻ p, ‖pairTransferDefect π l (φ n) t p‖ₑ ^ 2 ∂μ) Filter.atTop (nhds 0))
    (C : LinearMetricChains G) :
    ∃ ν : Measure (NormalizedPair G Λ), ∃ hν : IsFiniteMeasure ν, ν ≠ 0 ∧
      SMulInvariantMeasure G (NormalizedPair G Λ) ν ∧
      letI := hν
      ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g,
        ‖pairHeightL2 ν π hπ g - Lp.const 2 ν (A.symm (π g).toAdd)‖ ≤
          ε * dist 1 g + B := by
  obtain ⟨ν, hν, hν0, hνinv, θ, hθ, hθapprox⟩ :=
    inverseCoupling m μ A π l hπ hl hlA φ hφ hφm happrox
  let := hν
  let := hνinv
  let l' : G →* Multiplicative W := A.symm.toLinearMap.toAddMonoidHom.toMultiplicative.comp π
  refine ⟨ν, hν, hν0, hνinv, ?_⟩
  exact pairHeight_sublinear_of_linearChains ν C π l' hπ θ hθ hθapprox


end PolycyclicRecognition

end

end OAI
