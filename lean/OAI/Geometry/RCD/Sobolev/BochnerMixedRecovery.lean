import OAI.Geometry.RCD.Sobolev.BochnerMixedTerm
import OAI.Geometry.RCD.Sobolev.GammaL2Bound

namespace OAI

/-! # Removing the amplitude restriction from the Laplacian in mixed tests

Bounded Sobolev recovery converges strongly. With one bounded-gradient
factor, both remaining products are L² pairings, so the product identity
passes to an unbounded Sobolev Laplacian.
-/

open Set Filter MeasureTheory
open scoped NNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

private theorem mixed_bounded_test (f w b : SobolevSpace μ hQ) (d : Lp ℝ 2 μ)
    (A C : ℝ≥0)
    (hb : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ b x| ≤ A)
    (hw : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ w x| ≤ C)
    (hΔ : IsWeakLaplacian μ hQ f d) :
    weightedGamma μ hQ (SobolevSpace.toLp μ hQ w) f b +
      weightedGamma μ hQ (SobolevSpace.toLp μ hQ b) f w =
        -(∫ x, SobolevSpace.toLp μ hQ w x * d x * SobolevSpace.toLp μ hQ b x ∂μ) := by
  have hbn : ∀ᵐ x ∂μ, ‖SobolevSpace.toLp μ hQ b x‖ ≤ (A : ℝ) := by
    simpa only [Real.norm_eq_abs] using hb
  have hwn : ∀ᵐ x ∂μ, ‖SobolevSpace.toLp μ hQ w x‖ ≤ (C : ℝ) := by
    simpa only [Real.norm_eq_abs] using hw
  have hi₁ := (localGamma_memL1 μ hQ f b).bdd_mul
    (Lp.aestronglyMeasurable (SobolevSpace.toLp μ hQ w)) hwn
  have hi₂ := (localGamma_memL1 μ hQ f w).bdd_mul
    (Lp.aestronglyMeasurable (SobolevSpace.toLp μ hQ b)) hbn
  have htest := hΔ (SobolevSpace.product μ hQ b w A C)
  have hleft : energyForm μ hQ f (SobolevSpace.product μ hQ b w A C) =
      weightedGamma μ hQ (SobolevSpace.toLp μ hQ w) f b +
        weightedGamma μ hQ (SobolevSpace.toLp μ hQ b) f w := by
    rw [← integral_localGamma_eq_energyForm]
    unfold weightedGamma
    rw [← integral_add hi₁ hi₂]
    apply integral_congr_ae
    filter_upwards [localGamma_product_right μ hQ f b w A C hb hw] with x hx
    rw [hx]
    ring
  have hright : inner ℝ d (SobolevSpace.toLp μ hQ (SobolevSpace.product μ hQ b w A C)) =
      ∫ x, SobolevSpace.toLp μ hQ w x * d x * SobolevSpace.toLp μ hQ b x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [SobolevSpace.product_coe μ hQ b w A C hb hw] with x hx
    simp only [Real.inner_apply, hx]
    ring
  rw [hleft, hright] at htest
  exact htest

theorem weakLaplacian_mixed_identity_L2 (f d w : SobolevSpace μ hQ) (C L : ℝ≥0)
    (hw : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ w x| ≤ C)
    (hf : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ f x ≤ L)
    (hΔ : IsWeakLaplacian μ hQ f (SobolevSpace.toLp μ hQ d)) :
    weightedGamma μ hQ (SobolevSpace.toLp μ hQ w) f d +
      weightedGamma μ hQ (SobolevSpace.toLp μ hQ d) f w =
        -(∫ x, SobolevSpace.toLp μ hQ w x * (SobolevSpace.toLp μ hQ d x) ^ 2 ∂μ) := by
  let W := SobolevSpace.toLp μ hQ w
  let D := SobolevSpace.toLp μ hQ d
  have hwn : ∀ᵐ x ∂μ, ‖W x‖ ≤ (C : ℝ) := by simpa only [Real.norm_eq_abs] using hw
  have hQw := localGamma_memLp_of_bounded_gradient μ hQ f w L hf
  let Q := hQw.toLp (localGamma μ hQ f w)
  have hT : MemLp (fun x => W x * D x) 2 μ := by
    apply ((Lp.memLp D).norm.const_mul (C : ℝ)).mono'
      ((Lp.aestronglyMeasurable W).mul (Lp.aestronglyMeasurable D))
    filter_upwards [hwn] with x hx
    change ‖W x * D x‖ ≤ (C : ℝ) * ‖D x‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
  let T := hT.toLp (fun x => W x * D x)
  have hpair (b : SobolevSpace μ hQ) :
      (∫ x, W x * D x * SobolevSpace.toLp μ hQ b x ∂μ) =
        inner ℝ (SobolevSpace.toLp μ hQ b) T := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hT.coeFn_toLp] with x hx
    change T x = W x * D x at hx
    simp only [Real.inner_apply, hx]
    ring
  obtain ⟨b, hbd, hb⟩ := SobolevSpace.bounded_strong_recovery μ hQ d
  have hid (k : ℕ) : weightedGamma μ hQ W f (b k) +
      inner ℝ (SobolevSpace.toLp μ hQ (b k)) Q +
      inner ℝ (SobolevSpace.toLp μ hQ (b k)) T = 0 := by
    have hh := mixed_bounded_test μ hQ f w (b k) D k C (hb k) hw hΔ
    rw [weightedGamma_eq_L2_inner μ hQ f w hQw, hpair] at hh
    linarith
  have h₁ : Tendsto (fun k => weightedGamma μ hQ W f (b k)) atTop
      (𝓝 (weightedGamma μ hQ W f d)) :=
    (((weightedGammaCLM μ hQ (Lp.aestronglyMeasurable W) hwn) f).continuous.tendsto d).comp hbd
  have hlp := ((SobolevSpace.toLpCLM μ hQ).continuous.tendsto d).comp hbd
  have h₂ : Tendsto (fun k => inner ℝ (SobolevSpace.toLp μ hQ (b k)) Q) atTop
      (𝓝 (inner ℝ D Q)) := hlp.inner tendsto_const_nhds
  have h₃ : Tendsto (fun k => inner ℝ (SobolevSpace.toLp μ hQ (b k)) T) atTop
      (𝓝 (inner ℝ D T)) := hlp.inner tendsto_const_nhds
  have hz : weightedGamma μ hQ W f d + inner ℝ D Q + inner ℝ D T = 0 :=
    tendsto_nhds_unique ((h₁.add h₂).add h₃)
      (tendsto_const_nhds.congr' (Eventually.of_forall fun k => (hid k).symm))
  rw [← weightedGamma_eq_L2_inner μ hQ f w hQw, ← hpair d] at hz
  have he : (∫ x, W x * D x * D x ∂μ) = ∫ x, W x * (D x) ^ 2 ∂μ := by
    congr 1
    funext x
    ring
  rw [he] at hz
  linarith

end RegularPointCoordinates

end

end OAI
