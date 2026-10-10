import OAI.Analysis.IrrationalRotation.Rotation.RealWeightedPositiveDiagonal

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.PositiveDiagonalModel

variable {Y : Type*} [MeasurableSpace Y] {μ : Measure Y}

theorem integerIterate_measurePreserving (σ : Y ≃ᵐ Y)
    (hσ : MeasurePreserving σ μ μ) (k : ℤ) :
    MeasurePreserving (integerIterate σ k) μ μ := by
  cases k with
  | ofNat n => exact hσ.iterate n
  | negSucc n => exact (hσ.symm σ).iterate (n + 1)

theorem orbitWeightedShift_eq_of_ae_eq
    (σ : Y ≃ᵐ Y) (hσ : MeasurePreserving σ μ μ)
    (f g : Y → ℝ) (hf : Measurable f) (hg : Measurable g)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hfb : ∀ y, |f y| ≤ C) (hgb : ∀ y, |g y| ≤ D)
    (hfg : f =ᵐ[μ] g) :
    orbitWeightedShift (μ := μ) σ f C hC hfb hf = orbitWeightedShift (μ := μ) σ g D hD hgb hg := by
  have hall : ∀ᵐ y ∂μ, ∀ k : ℤ, f (integerIterate σ k y) = g (integerIterate σ k y) :=
    ae_all_iff.mpr fun k =>
      (integerIterate_measurePreserving σ hσ k).quasiMeasurePreserving.ae hfg
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  filter_upwards [realWeightedShift_ae (orbitArray σ f) C hC
      (fun y k => hfb (integerIterate σ k y))
      (fun k => (hf.comp (measurable_integerIterate σ k)).aestronglyMeasurable) ξ,
    realWeightedShift_ae (orbitArray σ g) D hD
      (fun y k => hgb (integerIterate σ k y))
      (fun k => (hg.comp (measurable_integerIterate σ k)).aestronglyMeasurable) ξ,
    hall] with y hfξ hgξ hy
  simp only [orbitWeightedShift]
  have hw : realWeight (orbitArray σ f) C
      (fun y k => hfb (integerIterate σ k y)) y =
      realWeight (orbitArray σ g) D
      (fun y k => hgb (integerIterate σ k y)) y := by
    ext k
    exact congrArg (fun r : ℝ => (r : ℂ)) (hy k)
  rw [hfξ, hgξ, hw]

end Invariant233.PositiveDiagonalModel

end

end OAI
