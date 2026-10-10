import OAI.GroupTheory.PolycyclicRecognition.Algebra.PairApproximation
import OAI.GroupTheory.PolycyclicRecognition.Analysis.PairMeanControl

namespace OAI

/-! # Compact coboundaries with the actual averaged homomorphism retained -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory
open scoped ENNReal NNReal

attribute [local instance] stationaryL2Action zeroMeanL2Action

/-- The published reduced-cohomology input supplies measurable compact-uniform
transfers for the concrete mean, whose metric control is already proved. -/
theorem normalizedPairMean_coboundary_approximation
    {G W : Type*} [Group G] [MetricSpace G] [ProperSpace G]
    [IsTopologicalGroup G] [IsIsometricSMul G G]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    [SecondCountableTopology W] [MeasurableSpace W] [BorelSpace W] {Λ : ℝ≥0}
    [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
    (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
    [ErgodicSMul G (NormalizedPair G Λ) μ] [μ.InnerRegularCompactLTTop]
    (hvan : ReducedCohomologyInput G (ZeroMeanL2 (W := W) μ))
    (π : G →* Multiplicative W) (hπ : Continuous fun g => (π g).toAdd) :
    ∃ φ : ℕ → NormalizedPair G Λ → W,
        (∀ n, MemLp (φ n) 2 μ) ∧ (∀ n, Measurable (φ n)) ∧
        ∀ Q : Set G, IsCompact Q →
          Filter.Tendsto (fun n => ⨆ t ∈ Q,
            ∫⁻ p, ‖pairTransferDefect π (normalizedPairMeanSlope μ π hπ) (φ n) t p‖ₑ ^ 2 ∂μ)
            Filter.atTop (nhds 0) := by
  let b := pairHeightL2 μ π hπ
  have hb : IsCocycle b := isCocycle_pairHeightL2 μ π hπ
  let l := l2MeanSlope μ b hb
  obtain ⟨ψ, hψ⟩ := stationary_coboundary_approximation_sequence μ hvan b
    (continuous_pairHeightL2 μ π hπ) hb
  let φ : ℕ → NormalizedPair G Λ → W :=
    fun n => (Lp.aestronglyMeasurable (ψ n)).mk (ψ n)
  have hae (n : ℕ) : ψ n =ᵐ[μ] φ n :=
    (Lp.aestronglyMeasurable (ψ n)).ae_eq_mk
  refine ⟨φ, fun n => (Lp.memLp (ψ n)).ae_eq (hae n),
    fun n => (Lp.aestronglyMeasurable (ψ n)).measurable_mk, ?_⟩
  intro Q hQ
  have heq (n : ℕ) (t : G) :
      (∫⁻ p, ‖pairTransferDefect π (normalizedPairMeanSlope μ π hπ) (φ n) t p‖ₑ ^ 2 ∂μ) =
      ENNReal.ofReal ‖b t + stationaryPullback μ t (ψ n) - ψ n -
        Lp.const 2 μ (l t).toAdd‖ ^ 2 := by
    rw [← lintegral_enorm_sq_L2]
    exact lintegral_congr_ae
      ((pairTransferDefect_ae_L2 μ π l hπ (ψ n) (φ n) (hae n) t).symm.fun_comp
        (fun w => ‖w‖ₑ ^ 2))
  simp_rw [heq]
  exact uniform_ofReal_sq_tendsto _ Q (hψ Q hQ)


end PolycyclicRecognition

end

end OAI
