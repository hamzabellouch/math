import OAI.GroupTheory.PolycyclicRecognition.Analysis.SequenceGoodProfileSegment
import OAI.GroupTheory.PolycyclicRecognition.Analysis.RescaledProfileLegs

namespace OAI

/-! # Supported sampled profiles control the actual large-scale flow legs -/

noncomputable section

namespace PolycyclicRecognition

open Module MeasureTheory Set Filter
open scoped Topology

/-- Combine the slow good-sheet selection, proved graded-flow convergence,
and the exact exponential-coordinate identity. The conclusion is expressed
at physical scale `r`, along the original one-parameter subgroup. -/
theorem exists_good_rescaled_flow_legs_sequence
    {L D N G W : Type*} [LieRing L] [LieAlgebra ℝ L]
    [Group D] [Group N] [Group G] [MeasurableSpace N]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {n c : ℕ}
    (ExpD : L → D) (b : Basis (Fin n) ℝ L) (cost : Fin n → ℝ)
    (a : DynkinCoefficients c 2)
    (hm : ∀ x y, ExpD (finiteDynkinPolynomial a ![x, y]) = ExpD x * ExpD y)
    (hweight : ∀ i j k, b.repr ⁅b i, b j⁆ k ≠ 0 → cost i + cost j ≤ cost k)
    (v : L) (hv : ∀ j, b.repr v j ≠ 0 → 1 ≤ cost j)
    (ι : N →* G) (κ : D →* G) (J : ℕ → G → W) (x : ℕ → G)
    (S : Set C((Fin n → ℝ), W)) [MeasurableSpace S] [BorelSpace S] [HasOuterApproxClosed S]
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (samples : ℕ → ProbabilityMeasure N) (profile : ℕ → N → S)
    (hp : ∀ r, Measurable (profile r)) (ν : ProbabilityMeasure S)
    (hν : Tendsto (fun r => ProbabilityMeasure.map (samples r) (profile r)) atTop (𝓝 ν))
    (hactual : ∀ r u z, (profile r u).val z =
      rescaledMapProfile (J r) (x r) (ι u) (max (Real.log (scale r)) 0)
        (fun z => κ (ExpD ((exponentialRescaleBasis b cost (max (Real.log (scale r)) 0)).equivFun.symm z))) z)
    (z : Fin n → ℝ) (T : ℝ) (U : Set (Fin n → ℝ)) (hU : IsOpen U)
    (hseg : ∀ t ∈ Icc 0 T,
      dynkinFlowMap a (gradedCoordinateBracket b cost) (gradedGenerator b cost 1 v) (z, t) ∈ U)
    {f : S} (hf : f ∈ (ν : Measure S).support) :
    ∃ (B : ℕ → Set N) (ζ : ℕ → ℝ),
      (∀ r, MeasurableSet (B r)) ∧ (∀ r, 0 < ζ r) ∧ Tendsto ζ atTop (𝓝 0) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => ((samples r : Measure N) (B r)).toReal) ∧
      ∀ η : ℝ, 0 < η → ∀ᶠ r in atTop, ∀ u ∈ B r, ∀ t ∈ Icc 0 T,
        ‖J r ((x r * ι u * κ (ExpD
            ((exponentialRescaleBasis b cost (max (Real.log (scale r)) 0)).equivFun.symm z))) *
              κ (ExpD ((scale r * t) • v))) - J r (x r) -
          scale r • f.val (dynkinFlowMap a (gradedCoordinateBracket b cost)
            (gradedGenerator b cost 1 v) (z, t))‖ ≤ scale r * (ζ r + η) := by
  let logscale := fun r : ℕ => max (Real.log (scale r)) 0
  let basis := fun r => exponentialRescaleBasis b cost (logscale r)
  let Ψ := fun r => dynkinFlowMap a (basisBracket (basis r))
    ((basis r).equivFun (Real.exp (logscale r) • v))
  let Ψ₀ := dynkinFlowMap a (gradedCoordinateBracket b cost) (gradedGenerator b cost 1 v)
  have hlogscale : Tendsto logscale atTop atTop :=
    tendsto_atTop_mono (fun r => le_max_left (Real.log (scale r)) 0)
      (Real.tendsto_log_atTop.comp hscale)
  have hΨ : Tendsto Ψ atTop (𝓝 Ψ₀) :=
    (rescaled_horizontal_flow_tendsto a b cost hweight v hv).comp hlogscale
  obtain ⟨Q, B, ζ, _, _, _, hB, hζ, hζlim, hmass, _, hgood⟩ :=
    exists_good_profiles_along_segment_sequence S scale hscale samples profile hp ν hν hf Ψ Ψ₀ hΨ z T U hU hseg
  refine ⟨B, ζ, hB, hζ, hζlim, hmass, ?_⟩
  intro η hη
  filter_upwards [hgood η hη, hscale.eventually (eventually_ge_atTop (1 : ℝ))] with r hr hr1
  have he : Real.exp (logscale r) = scale r := by
    dsimp [logscale]
    rw [max_eq_left (Real.log_nonneg hr1), Real.exp_log (lt_of_lt_of_le zero_lt_one hr1)]
  have hg : ∀ u ∈ B r, ∀ t ∈ Icc (0 : ℝ) T,
      ‖rescaledMapProfile (J r) (x r) (ι u) (logscale r)
          (fun y => κ (ExpD ((basis r).equivFun.symm y))) (Ψ r (z, t)) -
        f.val (Ψ₀ (z, t))‖ ≤ ζ r + η := by
    intro u hu t ht
    simpa only [hactual] using hr u hu t ht
  have hh := rescaled_profile_leg_bound ExpD (basis r) a hm ι κ (J r) (x r) (logscale r)
    v z T (B r) Ψ₀ f.val (ζ r + η) hg
  simpa only [he] using hh

end PolycyclicRecognition

end

end OAI
