import OAI.Geometry.RCD.Sobolev.UniformSlicesSpacetimeL2GoodSet

namespace OAI

/-! # Weighted spacetime value pairings along the common subsequence

Spatial and temporal tests need only be integrable. Uniform slice bounds
and the common countable exceptional set provide the domination.
-/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem uniform_slices_weighted_spacetime_limit
    {Y : Type*} [MeasurableSpace Y] [PseudoMetricSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] {δ M : ℝ}
    (f : ℕ → ℝ → Y → ℝ) (g : ℝ → Y → ℝ)
    (hf : ∀ k, Measurable (Function.uncurry (f k)))
    (hb : ∀ k t, t ∈ Ioo δ 1 → ∀ x, |f k t x| ≤ M)
    (N : Set ℝ) (hN : N.Countable)
    (hl : ∀ t ∈ Ioo δ 1, t ∉ N → TendstoUniformly (fun k => f k t) (g t) atTop)
    (θ : ℝ → ℝ) (hθ : Integrable θ (volume.restrict (Ioo δ 1)))
    (φ : Y → ℝ) (hφ : Integrable φ μ) :
    Tendsto (fun k => ∫ q : ℝ × Y, θ q.1*φ q.2*f k q.1 q.2
      ∂(volume.restrict (Ioo δ 1)).prod μ) atTop
      (𝓝 (∫ q : ℝ × Y, θ q.1*φ q.2*g q.1 q.2
        ∂(volume.restrict (Ioo δ 1)).prod μ)) := by
  let ν := (volume.restrict (Ioo δ 1)).prod μ
  have hw : Integrable (fun q : ℝ × Y => θ q.1*φ q.2) ν := hθ.mul_prod hφ
  have hi : Integrable (fun q : ℝ × Y => |θ q.1*φ q.2| * M) ν := hw.abs.mul_const M
  have hgood : ∀ᵐ t ∂volume.restrict (Ioo δ 1), t ∈ Ioo δ 1 ∧ t ∉ N :=
    (ae_restrict_mem measurableSet_Ioo).and (ae_restrict_of_ae (hN.ae_notMem volume))
  have hpair : ∀ᵐ q ∂ν, q.1 ∈ Ioo δ 1 ∧ q.1 ∉ N :=
    Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually hgood
  have hlim : ∀ᵐ q ∂ν, Tendsto (fun k => θ q.1*φ q.2*f k q.1 q.2) atTop
      (𝓝 (θ q.1*φ q.2*g q.1 q.2)) := by
    filter_upwards [hpair] with q hq
    exact ((hl q.1 hq.1 hq.2).tendsto_at q.2).const_mul _
  have hdom (k : ℕ) : ∀ᵐ q ∂ν, ‖θ q.1*φ q.2*f k q.1 q.2‖ ≤ |θ q.1*φ q.2| * M := by
    filter_upwards [hpair] with q hq
    rw [Real.norm_eq_abs,abs_mul]
    exact mul_le_mul_of_nonneg_left (hb k q.1 hq.1 q.2) (abs_nonneg _)
  exact tendsto_integral_of_dominated_convergence (fun q : ℝ × Y => |θ q.1*φ q.2| * M)
    (fun k => hw.aestronglyMeasurable.mul (hf k).aestronglyMeasurable) hi hdom hlim

end RegularPointCoordinates

end

end OAI
