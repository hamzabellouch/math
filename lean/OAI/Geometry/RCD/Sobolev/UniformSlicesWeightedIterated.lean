import OAI.Geometry.RCD.Sobolev.UniformSlicesWeightedLimit

namespace OAI

/-! # Iterated weak pairings along uniformly convergent time slices -/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem weighted_spacetime_integral_eq_iterated
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsFiniteMeasure μ]
    (τ : Measure ℝ) [IsFiniteMeasure τ] (f : ℝ → Y → ℝ)
    (hf : Measurable (Function.uncurry f)) {M : ℝ}
    (hb : ∀ᵐ q ∂τ.prod μ, |f q.1 q.2| ≤ M)
    (θ : ℝ → ℝ) (hθ : Integrable θ τ) (φ : Y → ℝ) (hφ : Integrable φ μ) :
    (∫ q : ℝ × Y, θ q.1*φ q.2*f q.1 q.2 ∂τ.prod μ) =
      ∫ t, θ t * ∫ x, φ x*f t x ∂μ ∂τ := by
  have hw : Integrable (fun q : ℝ × Y => θ q.1*φ q.2) (τ.prod μ) := hθ.mul_prod hφ
  have hi : Integrable (fun q : ℝ × Y => θ q.1*φ q.2*f q.1 q.2) (τ.prod μ) :=
    hw.mul_bdd hf.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hb)
  rw [integral_prod _ hi]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by
    dsimp only
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => mul_assoc _ _ _

theorem uniform_slices_weighted_iterated_limit
    {Y : Type*} [MeasurableSpace Y] [PseudoMetricSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] {δ M : ℝ}
    (f : ℕ → ℝ → Y → ℝ) (g : ℝ → Y → ℝ)
    (hf : ∀ k, Measurable (Function.uncurry (f k)))
    (hg : Measurable (Function.uncurry g))
    (hb : ∀ k t, t ∈ Ioo δ 1 → ∀ x, |f k t x| ≤ M)
    (N : Set ℝ) (hN : N.Countable)
    (hgb : ∀ t ∈ Ioo δ 1, t ∉ N → ∀ x, |g t x| ≤ M)
    (hl : ∀ t ∈ Ioo δ 1, t ∉ N → TendstoUniformly (fun k => f k t) (g t) atTop)
    (θ : ℝ → ℝ) (hθ : Integrable θ (volume.restrict (Ioo δ 1)))
    (φ : Y → ℝ) (hφ : Integrable φ μ) :
    Tendsto (fun k => ∫ t in Ioo δ 1, θ t * ∫ x, φ x*f k t x ∂μ) atTop
      (𝓝 (∫ t in Ioo δ 1, θ t * ∫ x, φ x*g t x ∂μ)) := by
  let τ := volume.restrict (Ioo δ 1)
  have hgood : ∀ᵐ t ∂τ, t ∈ Ioo δ 1 ∧ t ∉ N :=
    (ae_restrict_mem measurableSet_Ioo).and (ae_restrict_of_ae (hN.ae_notMem volume))
  have hpair : ∀ᵐ q ∂τ.prod μ, q.1 ∈ Ioo δ 1 ∧ q.1 ∉ N :=
    Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually hgood
  have hfb (k : ℕ) : ∀ᵐ q ∂τ.prod μ, |f k q.1 q.2| ≤ M :=
    hpair.mono fun q hq => hb k q.1 hq.1 q.2
  have hgb' : ∀ᵐ q ∂τ.prod μ, |g q.1 q.2| ≤ M :=
    hpair.mono fun q hq => hgb q.1 hq.1 hq.2 q.2
  have he (k : ℕ) := weighted_spacetime_integral_eq_iterated μ τ (f k) (hf k) (hfb k) θ hθ φ hφ
  have heg := weighted_spacetime_integral_eq_iterated μ τ g hg hgb' θ hθ φ hφ
  have hh := uniform_slices_weighted_spacetime_limit μ f g hf hb N hN hl θ hθ φ hφ
  dsimp only [τ] at he heg
  simpa only [he,heg] using hh

end RegularPointCoordinates

end

end OAI
