import OAI.GroupTheory.PolycyclicRecognition.Algebra.InverseTransferIdentity

namespace OAI

/-! # Inverse coupling with the prescribed inverse coefficient

Compact-uniform approximation of the forward height cocycle transfers to
the inverse section, with precisely the inverse linear coefficient. The
measure and the square-integrable transfer functions are constructed from
the pair-space charts and whole-fiber averages.
-/

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace PolycyclicRecognition

variable {G W : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [SecondCountableTopology G] [IsTopologicalGroup G] [IsIsometricSMul G G]
  {Λ : ℝ≥0} [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [SecondCountableTopology W]
  [MeasurableSpace W] [BorelSpace W]

/-- The manuscript's inverse-coupling construction, in the equivalent
squared-L² compact-uniform formulation. The inverse-section measure and all
inverse transfer functions are produced by the proof. -/
theorem inverseCoupling
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
        ∫⁻ p, ‖pairTransferDefect π l (φ n) t p‖ₑ ^ 2 ∂μ) Filter.atTop (nhds 0)) :
    ∃ ν : Measure (NormalizedPair G Λ), IsFiniteMeasure ν ∧ ν ≠ 0 ∧
      SMulInvariantMeasure G (NormalizedPair G Λ) ν ∧
      ∃ θ : ℕ → NormalizedPair G Λ → W, (∀ n, MemLp (θ n) 2 ν) ∧
        ∀ Q : Set G, IsCompact Q →
          Filter.Tendsto (fun n => ⨆ y ∈ Q,
            ∫⁻ p, ‖pairHeight π y p + θ n (normalizedTranslate y p) - θ n p -
              A.symm (π y).toAdd‖ₑ ^ 2 ∂ν) Filter.atTop (nhds 0) := by
  obtain ⟨ν, hνfin, hν0, hνinv, hprod⟩ := exists_inverseSection_measure m μ
  let := hνfin
  let := hνinv
  obtain ⟨B, hB, hB0⟩ := (Measure.Regular.exists_isCompact_not_null (μ := m)).mpr (NeZero.ne m)
  let θ := fun n => inverseTheta (normalizedRestriction m B) A π l (φ n)
  refine ⟨ν, hνfin, hν0, hνinv, θ, ?_, ?_⟩
  · intro n
    exact inverseTheta_memLp m μ ν hprod A π l hπ hl (hφ n) hB hB0
  · intro Q hQ
    obtain ⟨C, T, _hC, hT, hcenters, hincrements⟩ :=
      exists_inverse_compact_regions (Λ := Λ) hQ hB
    have hR := inverseAverageError_tendsto_uniform m μ ν hprod π l hπ hl φ hφ hφm
      hB hB0 hT hincrements hcenters (happrox T hT)
      (fun n t ht => le_iSup_of_le t (le_iSup_of_le ht le_rfl))
    exact inverseCocycleError_tendsto_uniform m μ ν hprod A π l hπ hl hlA φ hφ hB hB0 hR

end PolycyclicRecognition

end

end OAI
