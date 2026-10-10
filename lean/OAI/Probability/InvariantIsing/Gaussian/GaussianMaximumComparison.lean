import OAI.Probability.InvariantIsing.Core.FiniteGaussianMaximum

namespace OAI

/-! The finite Gaussian maximum comparison used for rectangular spectral edges. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing
variable {X : Type*} [Fintype X] [Nonempty X]

omit [Fintype X] [Nonempty X] in
lemma gaussianCross_scale_both {d : ℕ} (A C : X → Fin d → ℝ) (β : ℝ) (x y : X) :
    gaussianCross (fun x i => β*A x i) (fun x i => β*C x i) x y =
      β^2*gaussianCross A C x y := by
  unfold gaussianCross
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem finite_gaussian_maximum_comparison {d : ℕ} (C A : X → Fin (d+1) → ℝ)
    (hCA : ∀ x y, gaussianCross C A x y = 0)
    (hdiag : ∀ x, gaussianCross A A x x = gaussianCross C C x x)
    (hoff : ∀ x y, gaussianCross A A x y ≤ gaussianCross C C x y) :
    (∫ g, finiteGaussianMaximum C g ∂Measure.pi (fun _ : Fin (d+1) => gaussianReal 0 1)) ≤
      ∫ g, finiteGaussianMaximum A g ∂Measure.pi (fun _ : Fin (d+1) => gaussianReal 0 1) := by
  let μ := Measure.pi (fun _ : Fin (d+1) => gaussianReal 0 1)
  let MC := ∫ g, finiteGaussianMaximum C g ∂μ
  let MA := ∫ g, finiteGaussianMaximum A g ∂μ
  let K := Real.log (Fintype.card X)
  have hw : GibbsReference (fun _ : X => (1 : ℝ)) :=
    ⟨fun _ => zero_le_one,⟨Classical.choice ‹Nonempty X›,zero_lt_one⟩⟩
  have hbound (β : ℝ) (hβ : 0 < β) : β*MC ≤ β*MA+K := by
    let LC := fun g : Fin (d+1) → ℝ =>
      Real.log (finitePartition (fun _ : X => 1) (fun x => β*linearGaussian C g x))
    let LA := fun g : Fin (d+1) → ℝ =>
      Real.log (finitePartition (fun _ : X => 1) (fun x => β*linearGaussian A g x))
    have hiC : Integrable LC μ := by
      simpa only [zero_add] using integrable_log_finitePartition hw (fun _ => 0) C β
    have hiA : Integrable LA μ := by
      simpa only [zero_add] using integrable_log_finitePartition hw (fun _ => 0) A β
    have hlow : β*MC ≤ ∫ g, LC g ∂μ := by
      rw [← integral_const_mul]
      exact integral_mono ((finiteGaussianMaximum_integrable C).const_mul β) hiC
        (fun g => (finiteGaussianMaximum_log_bounds C g β hβ).1)
    have hupp : (∫ g, LA g ∂μ) ≤ β*MA+K := by
      have hconst : (∫ _ : Fin (d+1) → ℝ, K ∂μ) = K := by simp
      rw [← integral_const_mul,← hconst,← integral_add]
      · exact integral_mono hiA (((finiteGaussianMaximum_integrable A).const_mul β).add (integrable_const K))
          (fun g => (finiteGaussianMaximum_log_bounds A g β hβ).2)
      · exact (finiteGaussianMaximum_integrable A).const_mul β
      · exact integrable_const K
    have hmid : (∫ g, LC g ∂μ) ≤ ∫ g, LA g ∂μ := by
      have h := finite_gaussian_log_comparison hw (fun _ => 0)
        (fun x i => β*C x i) (fun x i => β*A x i)
        (fun x y => by rw [gaussianCross_scale_both,hCA x y,mul_zero])
        (fun x => by rw [gaussianCross_scale_both,gaussianCross_scale_both,hdiag x])
        (fun x y => by
          rw [gaussianCross_scale_both,gaussianCross_scale_both]
          exact mul_le_mul_of_nonneg_left (hoff x y) (sq_nonneg β))
      simpa only [linearGaussian_scale,zero_add] using h
    exact hlow.trans (hmid.trans hupp)
  change MC ≤ MA
  by_contra h
  have hpos : 0 < MC-MA := sub_pos.mpr (lt_of_not_ge h)
  let β := (|K|+1)/(MC-MA)
  have hβ : 0 < β := div_pos (by positivity) hpos
  have he : β*(MC-MA) = |K|+1 := div_mul_cancel₀ _ hpos.ne'
  have hh := hbound β hβ
  have hk := le_abs_self K
  nlinarith

end InvariantIsing

end

end OAI
