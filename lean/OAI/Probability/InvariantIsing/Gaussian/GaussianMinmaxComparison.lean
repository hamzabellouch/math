import OAI.Probability.InvariantIsing.Gaussian.GordonComparison
import OAI.Probability.InvariantIsing.Core.FiniteMinmax
import OAI.Probability.InvariantIsing.Gaussian.GaussianMaximumComparison

namespace OAI

/-! Removing the finite entropy error from Gordon's Gaussian comparison. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing
variable {U V : Type*} [Fintype U] [Nonempty U] [Fintype V] [Nonempty V]

theorem finite_gaussian_minmax_comparison {d : ℕ} (C A : U × V → Fin (d+1) → ℝ)
    (hCA : ∀ x y, gaussianCross C A x y = 0)
    (hrow : ∀ x u, gaussianCross A A x (u,x.2) = gaussianCross C C x (u,x.2))
    (hoff : ∀ x y, gaussianCross A A x y ≤ gaussianCross C C x y) :
    (∫ g, finiteMinmax (fun x => linearGaussian A g x)
      ∂Measure.pi (fun _ : Fin (d+1) => gaussianReal 0 1)) ≤
    ∫ g, finiteMinmax (fun x => linearGaussian C g x)
      ∂Measure.pi (fun _ : Fin (d+1) => gaussianReal 0 1) := by
  let μ := Measure.pi (fun _ : Fin (d+1) => gaussianReal 0 1)
  let MA := ∫ g, finiteMinmax (fun x => linearGaussian A g x) ∂μ
  let MC := ∫ g, finiteMinmax (fun x => linearGaussian C g x) ∂μ
  let K := Real.log (Fintype.card V)+Real.log (Fintype.card U)
  have hbound (β : ℝ) (hβ : 0 < β) : β*MA-Real.log (Fintype.card V) ≤
      β*MC+Real.log (Fintype.card U) := by
    let LA := fun g => gordonValue (fun x => β*linearGaussian A g x)
    let LC := fun g => gordonValue (fun x => β*linearGaussian C g x)
    have hiA : Integrable LA μ := by
      simpa only [zero_add,linearGaussian_scale] using
        integrable_gordonValue (fun _ => 0) (fun x i => β*A x i)
    have hiC : Integrable LC μ := by
      simpa only [zero_add,linearGaussian_scale] using
        integrable_gordonValue (fun _ => 0) (fun x i => β*C x i)
    have hl : β*MA-Real.log (Fintype.card V) ≤ ∫ g, LA g ∂μ := by
      have hc : (∫ _ : Fin (d+1) → ℝ, Real.log (Fintype.card V) ∂μ) =
          Real.log (Fintype.card V) := by simp
      change β*(∫ g, finiteMinmax (fun x => linearGaussian A g x) ∂μ)-_ ≤ _
      rw [← integral_const_mul,← hc,
        ← integral_sub ((finiteMinmax_linear_integrable A).const_mul β) (integrable_const _)]
      exact integral_mono (((finiteMinmax_linear_integrable A).const_mul β).sub (integrable_const _))
        hiA (fun g => (gordonValue_finiteMinmax_bounds _ β hβ).1)
    have hu : (∫ g, LC g ∂μ) ≤ β*MC+Real.log (Fintype.card U) := by
      have hc : (∫ _ : Fin (d+1) → ℝ, Real.log (Fintype.card U) ∂μ) =
          Real.log (Fintype.card U) := by simp
      change _ ≤ β*(∫ g, finiteMinmax (fun x => linearGaussian C g x) ∂μ)+_
      rw [← integral_const_mul,← hc,
        ← integral_add ((finiteMinmax_linear_integrable C).const_mul β) (integrable_const _)]
      exact integral_mono hiC
        (((finiteMinmax_linear_integrable C).const_mul β).add (integrable_const _))
        (fun g => (gordonValue_finiteMinmax_bounds _ β hβ).2)
    have hm : (∫ g, LA g ∂μ) ≤ ∫ g, LC g ∂μ := by
      have h := finite_gaussian_gordon_comparison (fun x i => β*C x i) (fun x i => β*A x i)
        (fun x y => by rw [gaussianCross_scale_both,hCA x y,mul_zero])
        (fun x u => by rw [gaussianCross_scale_both,gaussianCross_scale_both,hrow x u])
        (fun x y => by
          rw [gaussianCross_scale_both,gaussianCross_scale_both]
          exact mul_le_mul_of_nonneg_left (hoff x y) (sq_nonneg β))
      simpa only [linearGaussian_scale] using h
    exact hl.trans (hm.trans hu)
  change MA ≤ MC
  by_contra h
  have hp : 0 < MA-MC := sub_pos.mpr (lt_of_not_ge h)
  let β := (|K|+1)/(MA-MC)
  have hβ : 0 < β := div_pos (by positivity) hp
  have he : β*(MA-MC) = |K|+1 := div_mul_cancel₀ _ hp.ne'
  have hh := hbound β hβ
  have hk := le_abs_self K
  dsimp only [K] at hk he
  nlinarith

end InvariantIsing

end

end OAI
