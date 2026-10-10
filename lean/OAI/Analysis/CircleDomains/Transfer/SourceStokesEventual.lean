import OAI.Analysis.CircleDomains.Transfer.SourceStokesExclusion

namespace OAI

/-! Discard the finite initial segment before a source circuit has been
retained. The limit exclusion requires only eventual model identities. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity

 theorem boundaryExclusionSet_excludes_eventual_source_stokes
    (γ : ℕ → ℝ → ℂ) (γ₀ : ℝ → ℂ) (hγ₀ : Continuous γ₀)
    (O : ℕ → Set ℂ) (u : ℕ → ℂ → UnitAddCircle)
    (v : ℝ → ℝ) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (c : ℕ → ℂ) (c₀ : ℂ) (hc : Tendsto c atTop (𝓝 c₀))
    (r : ℕ → ℝ) (r₀ : ℝ≥0) (hrr : Tendsto r atTop (𝓝 (r₀ : ℝ)))
    (e : ℕ → ℝ) (he0 : Tendsto e atTop (𝓝 0))
    (hvalid : ∀ᶠ n in atTop, Differentiable ℝ (γ n) ∧ IsOpen (O n) ∧
      FiniteTransfer.SmoothCircleOn (u n) (O n) ∧
      (∀ t, γ n t ∈ O n) ∧ (∀ t, (v t : UnitAddCircle) = u n (γ n t)) ∧
      0 ≤ r n ∧ 0 ≤ e n ∧
      ∀ t ∈ Icc (0 : ℝ) 1, dist (γ n t) (γ₀ t) ≤ e n)
    (L I B : ℝ) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop,
      |circleFormIntegral (fun z => infDist z (closedBall (c n) (r n))) (u n) (γ n)| ≤
        Real.sqrt Real.pi * L * Real.sqrt (I + ε n) + 2 * Real.pi * L * (B + ε n)) :
    (boundaryCurveTrace γ₀ hγ₀, c₀, r₀) ∉
      boundaryExclusionSet v (Real.sqrt Real.pi * L * Real.sqrt I + 2 * Real.pi * L * B) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    (hv.continuous_deriv (by simp)).continuousOn
  have hestimate : ∀ᶠ n in atTop,
      dist (roundDiskBoundaryPairing (γ n) (c n) (r n) v)
        (roundDiskBoundaryPairing γ₀ c₀ (r₀ : ℝ) v) ≤
      (e n + dist (c n) c₀ + |r n - r₀|) * M := by
    filter_upwards [hvalid] with n hn
    obtain ⟨hdγ, _, _, _, _, hr, he, hclose⟩ := hn
    rw [Real.dist_eq]
    exact roundDiskBoundaryPairing_stability
      (γ n) γ₀ hdγ.continuous hγ₀ (c n) c₀ (s := (r₀ : ℝ)) hr r₀.property v hv he hclose
      (fun t ht => by simpa only [Real.norm_eq_abs] using hM t ht)
  have herror : Tendsto (fun n => (e n + dist (c n) c₀ + |r n - r₀|) * M) atTop (𝓝 0) := by
    simpa only [dist_self, sub_self, abs_zero, add_zero, zero_add, zero_mul] using
      ((he0.add (hc.dist (tendsto_const_nhds (x := c₀)))).add
        (hrr.sub (tendsto_const_nhds (x := (r₀ : ℝ)))).abs).mul_const M
  have hpair : Tendsto (fun n => roundDiskBoundaryPairing (γ n) (c n) (r n) v) atTop
      (𝓝 (roundDiskBoundaryPairing γ₀ c₀ (r₀ : ℝ) v)) :=
    tendsto_iff_dist_tendsto_zero.mpr
      (squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg)) hestimate herror)
  have hpairbound : ∀ᶠ n in atTop,
      |roundDiskBoundaryPairing (γ n) (c n) (r n) v| ≤
        Real.sqrt Real.pi * L * Real.sqrt (I + ε n) + 2 * Real.pi * L * (B + ε n) := by
    filter_upwards [hvalid, hbound] with n hn hb
    obtain ⟨hdγ, hO, hu, hγO, hproj, _, _, _⟩ := hn
    rwa [circleFormIntegral_eq_roundBoundaryPairing (O n) hO (u n) hu (γ n)
      hdγ hγO v hv.continuous hproj (c n) (r n)] at hb
  have hsum : Tendsto (fun n => I + ε n) atTop (𝓝 I) := by
    simpa only [add_zero] using tendsto_const_nhds.add hε
  have hsqrt := (Real.continuous_sqrt.tendsto I).comp hsum
  have hbudget : Tendsto
      (fun n => Real.sqrt Real.pi * L * Real.sqrt (I + ε n) + 2 * Real.pi * L * (B + ε n))
      atTop (𝓝 (Real.sqrt Real.pi * L * Real.sqrt I + 2 * Real.pi * L * B)) := by
    simpa only [Function.comp_apply, add_zero] using
      (hsqrt.const_mul (Real.sqrt Real.pi * L)).add
        ((tendsto_const_nhds.add hε).const_mul (2 * Real.pi * L))
  change ¬ _ < |boundaryPairFunctional v _|
  rw [boundaryPairFunctional_trace]
  exact not_lt_of_ge (le_of_tendsto_of_tendsto hpair.abs hbudget hpairbound)

end CircleDomainRigidity

end

end OAI
