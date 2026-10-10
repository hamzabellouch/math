import OAI.Probability.InvariantIsing.Cavity.CavityFiniteHeightLimit
import OAI.Probability.InvariantIsing.Cavity.CavityStrictUniformPath

namespace OAI

/-! Strict interior overlap approximations retain the same finite
spectral-block limit as the uniform cell-average cascades. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

lemma cavity_cascade_clamp_law (n : ℕ) (b a : ℕ → ℝ) :
    cascadeCompactLaw n b (fun i => a (cavityFiniteLevel n i)) = cascadeCompactLaw n b a := by
  have he : (fun σ : ℕ → LabeledLeaf n => compactScalarArray (diagonalPatch 1
      (cascadeScalarArray n (fun i => a (cavityFiniteLevel n i)) σ))) =
      (fun σ => compactScalarArray (diagonalPatch 1 (cascadeScalarArray n a σ))) := by
    funext σ
    congr 1
    funext i j
    dsimp only [diagonalPatch, cascadeScalarArray]
    split_ifs
    · rfl
    · change a (min (labeledCommonDepth n (σ i) (σ j)) n) = _
      rw [min_eq_left (labeledCommonDepth_le n _ _)]
  simp only [cascadeCompactLaw, he]
  rfl

theorem cavity_strict_uniform_block_error {m r : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) (F : SpectralBlock m r →ᵇ ℝ) :
    Tendsto (fun n =>
      (∫ x, F (cavitySynchronizedBlock (cavityCanonicalDiagonal rho lam hrho hsum p)
          (cavityCanonicalLabel rho lam hrho hsum p) (arrayBlock spinArray r x))
        ∂(cascadeCompactLaw n (uniformExponent n)
          (fun i => cavityStrictUniformLevels p n (cavityFiniteLevel n i)) : Measure JointArray)) -
      ∫ x, F (cavitySynchronizedBlock (cavityCanonicalDiagonal rho lam hrho hsum p)
          (cavityCanonicalLabel rho lam hrho hsum p) (arrayBlock spinArray r x))
        ∂(cascadeCompactLaw n (uniformExponent n) (uniformCellAverage p n) : Measure JointArray))
      atTop (𝓝 0) := by
  have he := cavity_finite_height_integral_error rho lam hrho hsum p
    (cavityStrictUniformLevels p) (fun n i => uniformCellAverage p n i)
    (fun n => (cavityStrictUniformLevels_strict p n).monotone)
    (fun n i j hij => uniformCellAverage_monotone p.monotone
      (fun s => ⟨p.nonneg s, p.le_one s⟩) n hij)
    (fun n i => ⟨(cavityStrictUniformLevels_mem p n i).1.le,
      (cavityStrictUniformLevels_mem p n i).2.le⟩)
    (fun n i => uniformCellAverage_mem p.monotone
      (fun s => ⟨p.nonneg s, p.le_one s⟩) n i)
    uniformExponent (fun n => 1 / ((n : ℝ) + 1))
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    (fun n i => cavityStrictLevels_dist _
      (fun i => uniformCellAverage_mem p.monotone
        (fun s => ⟨p.nonneg s, p.le_one s⟩) n i) (cavity_uniform_epsilon n).1.le i) F
  simpa only [cavity_cascade_clamp_law] using he

end InvariantIsing

end

end OAI
