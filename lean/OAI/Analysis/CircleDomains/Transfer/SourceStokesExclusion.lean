import OAI.Analysis.CircleDomains.Topology.BoundaryPairNeighborhood

namespace OAI

/-! The exact square-root source-energy bound passes to the fixed
boundary-pair exclusion under vanishing transfer errors. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity

 theorem boundaryExclusionSet_excludes_source_stokes_limit
    (γ : ℕ → ℝ → ℂ) (γ₀ : ℝ → ℂ)
    (hγ : ∀ n, Differentiable ℝ (γ n)) (hγ₀ : Continuous γ₀)
    (O : ℕ → Set ℂ) (hO : ∀ n, IsOpen (O n))
    (u : ℕ → ℂ → UnitAddCircle) (hu : ∀ n, FiniteTransfer.SmoothCircleOn (u n) (O n))
    (hγO : ∀ n t, γ n t ∈ O n)
    (v : ℝ → ℝ) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hproj : ∀ n t, (v t : UnitAddCircle) = u n (γ n t))
    (c : ℕ → ℂ) (c₀ : ℂ) (hc : Tendsto c atTop (𝓝 c₀))
    (r : ℕ → ℝ) (r₀ : ℝ≥0) (hr : ∀ n, 0 ≤ r n)
    (hrr : Tendsto r atTop (𝓝 (r₀ : ℝ)))
    (e : ℕ → ℝ) (he : ∀ n, 0 ≤ e n) (he0 : Tendsto e atTop (𝓝 0))
    (hclose : ∀ n, ∀ t ∈ Icc (0 : ℝ) 1, dist (γ n t) (γ₀ t) ≤ e n)
    (L I B : ℝ) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop,
      |circleFormIntegral (fun z => infDist z (closedBall (c n) (r n))) (u n) (γ n)| ≤
        Real.sqrt Real.pi * L * (Real.sqrt (I + ε n)) + 2 * Real.pi * L * (B + ε n)) :
    (boundaryCurveTrace γ₀ hγ₀, c₀, r₀) ∉
      boundaryExclusionSet v (Real.sqrt Real.pi * L * Real.sqrt I + 2 * Real.pi * L * B) := by
  have herror : Tendsto (fun n => Real.sqrt (I + ε n) - Real.sqrt I) atTop (𝓝 0) := by
    have h := ((Real.continuous_sqrt.tendsto I).comp
      (show Tendsto (fun n => I + ε n) atTop (𝓝 I) from by
        simpa only [add_zero] using tendsto_const_nhds.add hε)).sub_const (Real.sqrt I)
    simpa only [Function.comp_apply, sub_self] using h
  apply boundaryExclusionSet_excludes_stokes_limit γ γ₀ hγ hγ₀ O hO u hu hγO v hv hproj
    c c₀ hc r r₀ hr hrr e he he0 hclose L (Real.sqrt I) B
    (fun n => Real.sqrt (I + ε n) - Real.sqrt I) ε herror hε
  filter_upwards [hbound] with n hn
  have heq : Real.sqrt I + (Real.sqrt (I + ε n) - Real.sqrt I) = Real.sqrt (I + ε n) := by ring
  simpa only [heq] using hn

end CircleDomainRigidity

end

end OAI
