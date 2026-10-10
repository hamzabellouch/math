import OAI.GroupTheory.PolycyclicRecognition.Algebra.PairApproximation
import OAI.GroupTheory.PolycyclicRecognition.Algebra.InverseCoupling
import OAI.GroupTheory.PolycyclicRecognition.Algebra.GeodesicWords

namespace OAI

/-! # Sublinear height errors from the coupled transfers

The finite invariant measure on the inverse section need not be ergodic.
The transfers already constructed there suffice for the same word estimate.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace PolycyclicRecognition

attribute [local instance] stationaryL2Action

variable {G W : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] {Λ : ℝ≥0}
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (μ : Measure (NormalizedPair G Λ)) [IsFiniteMeasure μ]
  [SMulInvariantMeasure G (NormalizedPair G Λ) μ]

/-- Subtracting any continuous height homomorphism preserves the cocycle
identity, independently of any ergodicity or averaging assertion. -/
theorem isCocycle_pairHeight_sub_hom
    (π l : G →* Multiplicative W) (hπ : Continuous fun g => (π g).toAdd) :
    IsCocycle (fun g => pairHeightL2 μ π hπ g - Lp.const 2 μ (l g).toAdd) := by
  intro g h
  have hb := isCocycle_pairHeightL2 μ π hπ g h
  change pairHeightL2 μ π hπ (g * h) - Lp.const 2 μ (l (g * h)).toAdd =
    (pairHeightL2 μ π hπ g - Lp.const 2 μ (l g).toAdd) +
      stationaryPullback μ g (pairHeightL2 μ π hπ h - Lp.const 2 μ (l h).toAdd)
  rw [hb, map_sub, stationaryPullback_const_finite, map_mul l]
  simp only [toAdd_mul, map_add]
  change pairHeightL2 μ π hπ g + stationaryPullback μ g (pairHeightL2 μ π hπ h) -
    (Lp.const 2 μ (l g).toAdd + Lp.const 2 μ (l h).toAdd) = _
  abel

/-- A compact-uniform squared-error estimate gives an actual small
coboundary in the Hilbert space, for a finite invariant measure. -/
theorem pairHeight_coboundary_of_squared_errors
    (π l : G →* Multiplicative W) (hπ : Continuous fun g => (π g).toAdd)
    (φ : ℕ → NormalizedPair G Λ → W) (hφ : ∀ n, MemLp (φ n) 2 μ)
    (Q : Set G)
    (happrox : Filter.Tendsto (fun n => ⨆ t ∈ Q,
      ∫⁻ p, ‖pairTransferDefect π l (φ n) t p‖ₑ ^ 2 ∂μ) Filter.atTop (nhds 0)) :
    ∀ ε : ℝ, 0 < ε → ∃ v : Lp W 2 μ, ∀ q ∈ Q,
      ‖(pairHeightL2 μ π hπ q - Lp.const 2 μ (l q).toAdd) + q • v - v‖ ≤ ε := by
  intro ε hε
  obtain ⟨n, hn⟩ := (ENNReal.tendsto_nhds_zero.mp happrox
    (ENNReal.ofReal (ε ^ 2)) (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hε))).exists
  let v := (hφ n).toLp (φ n)
  refine ⟨v, fun q hq => ?_⟩
  let e := pairHeightL2 μ π hπ q + stationaryPullback μ q v - v -
    Lp.const 2 μ (l q).toAdd
  have heq : (∫⁻ p, ‖pairTransferDefect π l (φ n) q p‖ₑ ^ 2 ∂μ) =
      ENNReal.ofReal ‖e‖ ^ 2 := by
    rw [← lintegral_enorm_sq_L2]
    exact lintegral_congr_ae
      ((pairTransferDefect_ae_L2 μ π l hπ v (φ n) (hφ n).coeFn_toLp q).symm.fun_comp
        (fun w => ‖w‖ₑ ^ 2))
  have he : ENNReal.ofReal (‖e‖ ^ 2) ≤ ENNReal.ofReal (ε ^ 2) := by
    rw [ENNReal.ofReal_pow (norm_nonneg e), ← heq]
    calc
      _ ≤ ⨆ t ∈ Q, ∫⁻ p, ‖pairTransferDefect π l (φ n) t p‖ₑ ^ 2 ∂μ :=
        le_iSup_of_le q (le_iSup_of_le hq le_rfl)
      _ ≤ _ := hn
  have hsq := (ENNReal.ofReal_le_ofReal_iff (sq_nonneg ε)).mp he
  have he' : ‖e‖ ≤ ε := by nlinarith [norm_nonneg e]
  convert he' using 1
  congr 1
  dsimp [e]
  change (pairHeightL2 μ π hπ q - Lp.const 2 μ (l q).toAdd) +
    stationaryPullback μ q v - v = _
  abel

/-- Compact-uniform transfer errors imply the global sublinear word bound.
This applies directly to the finite measure constructed by inverse coupling. -/
theorem pairHeight_sublinear_of_squared_errors
    (π l : G →* Multiplicative W) (hπ : Continuous fun g => (π g).toAdd)
    (φ : ℕ → NormalizedPair G Λ → W) (hφ : ∀ n, MemLp (φ n) 2 μ)
    (Q : Set G) (length : G → ℝ) (hlen : ∀ g, 0 ≤ length g)
    {a : ℝ} (ha : 0 ≤ a)
    (hword : ∀ g, ∃ w : List G, (∀ q ∈ w, q ∈ Q) ∧ w.prod = g ∧
      (w.length : ℝ) ≤ a * length g + a)
    (happrox : Filter.Tendsto (fun n => ⨆ t ∈ Q,
      ∫⁻ p, ‖pairTransferDefect π l (φ n) t p‖ₑ ^ 2 ∂μ) Filter.atTop (nhds 0)) :
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g,
      ‖pairHeightL2 μ π hπ g - Lp.const 2 μ (l g).toAdd‖ ≤ ε * length g + B := by
  exact (isCocycle_pairHeight_sub_hom μ π l hπ).sublinear_of_coboundary_approximation
    Q length hlen ha hword (pairHeight_coboundary_of_squared_errors μ π l hπ φ hφ Q happrox)

/-- For a proper group with minimizing paths, compact-uniform transfer
approximation alone supplies metric sublinearity. -/
theorem pairHeight_sublinear_of_minimizing_paths
    (π l : G →* Multiplicative W) (hπ : Continuous fun g => (π g).toAdd)
    (φ : ℕ → NormalizedPair G Λ → W) (hφ : ∀ n, MemLp (φ n) 2 μ)
    (happrox : ∀ Q : Set G, IsCompact Q →
      Filter.Tendsto (fun n => ⨆ t ∈ Q,
        ∫⁻ p, ‖pairTransferDefect π l (φ n) t p‖ₑ ^ 2 ∂μ) Filter.atTop (nhds 0))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u ∈ Set.Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|) :
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g,
      ‖pairHeightL2 μ π hπ g - Lp.const 2 μ (l g).toAdd‖ ≤ ε * dist 1 g + B := by
  apply pairHeight_sublinear_of_squared_errors μ π l hπ φ hφ (Metric.closedBall 1 1)
    (fun g => dist 1 g) (fun _ => dist_nonneg) (a := 1) (by norm_num)
  · simpa using wordFactorization_of_minimizing_paths hpath
  · exact happrox _ (isCompact_closedBall 1 1)

/-- The actual inverse coupling supplies a sublinear inverse height error
with exactly the inverse coefficient. No ergodicity of its finite measure
and no second reduced-cohomology hypothesis are required. -/
theorem inverseCoupling_sublinear
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
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u ∈ Set.Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|) :
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
  exact pairHeight_sublinear_of_minimizing_paths ν π l' hπ θ hθ hθapprox hpath

end PolycyclicRecognition

end

end OAI
