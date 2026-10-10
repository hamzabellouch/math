import OAI.GroupTheory.PolycyclicRecognition.Analysis.StationaryApproximation
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CouplingTransfer

namespace OAI

/-! # Measurable approximation of the actual pair-height cocycle -/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace PolycyclicRecognition

attribute [local instance] stationaryL2Action zeroMeanL2Action

variable {G W : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] {Λ : ℝ≥0}
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (μ : Measure (NormalizedPair G Λ)) [IsFiniteMeasure μ]
  [SMulInvariantMeasure G (NormalizedPair G Λ) μ]

/-- A representative of an L² transfer gives exactly the pointwise defect
of the height cocycle, up to the unavoidable null set for a fixed group element. -/
theorem pairTransferDefect_ae_L2
    (π l : G →* Multiplicative W) (hπ : Continuous fun g => (π g).toAdd)
    (v : Lp W 2 μ) (φ : NormalizedPair G Λ → W) (hv : v =ᵐ[μ] φ) (g : G) :
    (pairHeightL2 μ π hπ g + stationaryPullback μ g v - v -
      Lp.const 2 μ (l g).toAdd : Lp W 2 μ) =ᵐ[μ] pairTransferDefect π l φ g := by
  have hb : pairHeightL2 μ π hπ g =ᵐ[μ] pairHeight π g :=
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ (pairHeightProfile π hπ g)
  have hpull : stationaryPullback μ g v =ᵐ[μ] fun p => v (g⁻¹ • p) :=
    Lp.coeFn_compMeasurePreserving v (measurePreserving_smul g⁻¹ μ)
  have hvpull := (measurePreserving_smul g⁻¹ μ).quasiMeasurePreserving.ae_eq_comp hv
  filter_upwards [hb, hpull, hvpull, hv,
    Lp.coeFn_add (pairHeightL2 μ π hπ g) (stationaryPullback μ g v),
    Lp.coeFn_sub (pairHeightL2 μ π hπ g + stationaryPullback μ g v) v,
    Lp.coeFn_sub (pairHeightL2 μ π hπ g + stationaryPullback μ g v - v)
      (Lp.const 2 μ (l g).toAdd), Lp.coeFn_const 2 μ (l g).toAdd]
    with p hb hpull hvpull hv hadd hsub hsub' hc
  simp only [Pi.add_apply, Pi.sub_apply, Function.comp_apply] at *
  rw [hsub', hsub, hadd, hb, hpull, hvpull, hv, hc]
  change pairHeight π g p + φ (normalizedTranslate g⁻¹⁻¹ p) - φ p - (l g).toAdd = _
  simp only [inv_inv, pairTransferDefect]

/-- Uniformly small nonnegative real errors have uniformly vanishing squared
extended-real errors. This handles the supremum over an entire compact set. -/
theorem uniform_ofReal_sq_tendsto {T : Type*} (f : ℕ → T → ℝ) (Q : Set T)
    (hsmall : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in Filter.atTop, ∀ q ∈ Q, f n q ≤ ε) :
    Filter.Tendsto (fun n => ⨆ q ∈ Q, ENNReal.ofReal (f n q) ^ 2)
      Filter.atTop (nhds 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  have ht : Filter.Tendsto (fun k : ℕ =>
      ENNReal.ofReal (1 / ((k : ℝ) + 1)) ^ 2) Filter.atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.pow (n := 2)
      (ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat)
  obtain ⟨k, hk⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  filter_upwards [hsmall (1 / ((k : ℝ) + 1)) (by positivity)] with n hn
  refine iSup_le fun q => iSup_le fun hq => (pow_le_pow_left₀ (by positivity) ?_ 2).trans hk.le
  exact ENNReal.ofReal_le_ofReal (hn q hq)

/-- The precise published reduced-cohomology input produces measurable
square-integrable transfers for the actual pair-height cocycle. Their squared
defects vanish uniformly on every compact subset of the group. -/
theorem normalizedPair_coboundary_approximation
    {G W : Type*} [Group G] [MetricSpace G] [ProperSpace G]
    [IsTopologicalGroup G] [IsIsometricSMul G G]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    [SecondCountableTopology W] [MeasurableSpace W] [BorelSpace W] {Λ : ℝ≥0}
    [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
    (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
    [ErgodicSMul G (NormalizedPair G Λ) μ] [μ.InnerRegularCompactLTTop]
    (hvan : ReducedCohomologyInput G (ZeroMeanL2 (W := W) μ))
    (π : G →* Multiplicative W) (hπ : Continuous fun g => (π g).toAdd) :
    ∃ l : G →* Multiplicative W, (Continuous fun g => (l g).toAdd) ∧
      ∃ φ : ℕ → NormalizedPair G Λ → W,
        (∀ n, MemLp (φ n) 2 μ) ∧ (∀ n, Measurable (φ n)) ∧
        ∀ Q : Set G, IsCompact Q →
          Filter.Tendsto (fun n => ⨆ t ∈ Q,
            ∫⁻ p, ‖pairTransferDefect π l (φ n) t p‖ₑ ^ 2 ∂μ)
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
  refine ⟨l, (stationaryL2Mean μ).continuous.comp (continuous_pairHeightL2 μ π hπ),
    φ, fun n => (Lp.memLp (ψ n)).ae_eq (hae n),
    fun n => (Lp.aestronglyMeasurable (ψ n)).measurable_mk, ?_⟩
  intro Q hQ
  have heq (n : ℕ) (t : G) :
      (∫⁻ p, ‖pairTransferDefect π l (φ n) t p‖ₑ ^ 2 ∂μ) =
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
