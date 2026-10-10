import OAI.GroupTheory.PolycyclicRecognition.Analysis.SubexponentialPathPacking
import OAI.GroupTheory.PolycyclicRecognition.Analysis.FixedSlicePacking

namespace OAI

/-! # Accessible fixed-slice volume and image-path growth -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Filter Metric Set
open scoped NNReal ENNReal Topology Pointwise

/-- The geometric packing comparison for compact accessible endpoint sets.
Haar volume supplies the lower count; only the image paths and the existing
ambient path-packing theorem are used for the upper count. -/
theorem fixedSlice_volume_exponent_le
    {N D G W : Type*} [Group N] [Group D] [Group G]
    [TopologicalSpace N] [MeasurableSpace N] [MeasurableMul N]
    [MetricSpace G] [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {Λ : ℝ≥0}
    (ι : N →* G) (κ : D →* G) (φ : D →* MulAut N)
    (μ : Measure N) [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ]
    (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
    (hconj : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (hι : Topology.IsClosedEmbedding ι)
    (S : ℝ → Set N) (hS : ∀ r, IsCompact (S r))
    (x : ℝ → G) (d : ℝ → D) (a : ℝ → G) (f : ℝ → NormalizedPair G Λ)
    (π : G →* Multiplicative W) (E : Set W) (P : Set W → ℝ)
    {p K C A : ℝ} (hΛ : 0 < (Λ : ℝ)) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hmass : HasSubexponentialLowerBound (fun r => (μ (S r)).toReal / Real.exp (r * p)))
    (hpaths : ∀ η : ℝ, 0 < η → ∀ᶠ r in atTop, ∀ u ∈ S r,
      ∃ γ : Path (a r) (x r * ι u * κ (d r)),
        PathMetricBound γ (C * r) (C * (1 + Real.log (2 + r))) ∧
        ∀ t, ∃ z ∈ E,
          ‖(π ((f r).val.1 (γ t))).toAdd - (π ((f r).val.1 (a r))).toAdd - r • z‖ ≤
            η * r + K * Λ * C * (1 + Real.log (2 + r)))
    (hA : 0 < A) (k : ℕ)
    (hupper : ∀ {r L κ' B ε : ℝ}, 0 < r → 0 ≤ L → 0 ≤ κ' → 0 ≤ ε →
      K * (κ' + 2) + B ≤ r * ε → ∀ s : Finset G,
      (∀ y ∈ s, ∀ z ∈ s, y ≠ z → 1 ≤ dist y z) →
      (∀ y ∈ s, ∃ γ : Path (1 : G) y, PathMetricBound γ L κ' ∧
        ∀ t, ∃ z ∈ E, ‖(π (γ t)).toAdd - r • z‖ ≤ B) →
      (s.card : ℝ) ≤ A * (3 + (L + 1) * (κ' + 2)) ^ k *
        Real.exp (r * P (E + closedBall 0 ε))) :
    ∀ ε : ℝ, 0 < ε → p ≤ P (E + closedBall 0 ε) := by
  let ρ := (Λ : ℝ) * ((Λ : ℝ) + 1)
  have hρ : 0 < ρ := mul_pos hΛ (by linarith)
  let Q := μ (ι ⁻¹' closedBall (1 : G) ρ)
  have hQ : Q < ⊤ := fixedSlice_packing_constant_lt_top ι μ hι ρ
  apply exponent_le_of_subexponential_image_paths π E P hmass hΛ hK hC hQ hA k
  · intro η hη
    filter_upwards [hpaths η hη] with r hr
    obtain ⟨s, hs, hsep, hmass'⟩ := exists_fixedSlice_separated_net_of_compact
      ι κ φ μ hφ hconj hι.continuous (x r) (d r) (hS r) (Subset.refl (S r)) hρ
    refine ⟨f r, a r, s, hsep, ?_, ?_⟩
    · have hv : μ (S r) ≠ ⊤ := (hS r).measure_lt_top.ne
      have he : ENNReal.ofReal ((μ (S r)).toReal / Real.exp (r * p)) *
          ENNReal.ofReal (Real.exp (r * p)) = μ (S r) := by
        rw [← ENNReal.ofReal_mul (div_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le)]
        rw [div_mul_cancel₀ _ (Real.exp_ne_zero _), ENNReal.ofReal_toReal hv]
      rw [he]
      exact hmass'
    · intro g hg
      obtain ⟨u, hu, rfl⟩ := hs hg
      exact hr u hu
  · exact hupper

end PolycyclicRecognition

end

end OAI
