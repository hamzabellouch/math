import OAI.NumberTheory.CubicMoment.Estimates.StructuredHeightContinuity

namespace OAI

/-! Positive, normalized two-sided height averaging. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

def dyadicHeightMean (f : ℝ → ℝ) (T : ℝ) : ℝ :=
  ((∫ t in T..2*T, f t)+(∫ t in -2*T..-T, f t))/T

lemma dyadicHeightMean_mono {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {T : ℝ} (hT : 0 < T)
    (h : ∀ t ∈ Set.Icc (-2*T) (2*T), f t ≤ g t) :
    dyadicHeightMean f T ≤ dyadicHeightMean g T := by
  apply div_le_div_of_nonneg_right _ hT.le
  apply add_le_add
  · apply intervalIntegral.integral_mono_on (by linarith : T ≤ 2*T)
      (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)
    intro t ht
    exact h t ⟨by linarith [ht.1],ht.2⟩
  · apply intervalIntegral.integral_mono_on (by linarith : -2*T ≤ -T)
      (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)
    intro t ht
    exact h t ⟨ht.1,by linarith [ht.2]⟩

lemma dyadicHeightMean_const (C : ℝ) {T : ℝ} (hT : T ≠ 0) :
    dyadicHeightMean (fun _ => C) T = 2*C := by
  simp only [dyadicHeightMean,intervalIntegral.integral_const,smul_eq_mul]
  field_simp
  ring

lemma dyadicHeightMean_le_const {f : ℝ → ℝ} (hf : Continuous f)
    {T C : ℝ} (hT : 0 < T)
    (h : ∀ t ∈ Set.Icc (-2*T) (2*T), f t ≤ C) :
    dyadicHeightMean f T ≤ 2*C :=
  (dyadicHeightMean_mono hf continuous_const hT h).trans_eq
    (dyadicHeightMean_const C hT.ne')

lemma dyadicHeightMean_add {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (T : ℝ) :
    dyadicHeightMean (fun t => f t+g t) T = dyadicHeightMean f T+dyadicHeightMean g T := by
  simp only [dyadicHeightMean,intervalIntegral.integral_add
    (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
  ring

lemma dyadicHeightMean_add_of_integrable {f g : ℝ → ℝ} (T : ℝ)
    (hfp : IntervalIntegrable f volume T (2*T)) (hfn : IntervalIntegrable f volume (-2*T) (-T))
    (hgp : IntervalIntegrable g volume T (2*T)) (hgn : IntervalIntegrable g volume (-2*T) (-T)) :
    dyadicHeightMean (fun t => f t+g t) T = dyadicHeightMean f T+dyadicHeightMean g T := by
  simp only [dyadicHeightMean,intervalIntegral.integral_add hfp hgp,
    intervalIntegral.integral_add hfn hgn]
  ring

lemma dyadicHeightMean_sum {α : Type*} (S : Finset α) (f : α → ℝ → ℝ)
    (hf : ∀ a ∈ S, Continuous (f a)) (T : ℝ) :
    dyadicHeightMean (fun t => ∑ a ∈ S, f a t) T = ∑ a ∈ S, dyadicHeightMean (f a) T :=
  finite_dyadic_integral_sum S f hf T

lemma dyadicHeightMean_const_mul (c : ℝ) (f : ℝ → ℝ) (T : ℝ) :
    dyadicHeightMean (fun t => c*f t) T = c*dyadicHeightMean f T := by
  simp only [dyadicHeightMean,intervalIntegral.integral_const_mul]
  ring

lemma dyadicHeightMean_neg (f : ℝ → ℝ) (T : ℝ) :
    dyadicHeightMean (fun t => f (-t)) T = dyadicHeightMean f T := by
  have h₁ : -(-2*T) = 2*T := by ring
  have h₂ : -(2*T) = -2*T := by ring
  simp only [dyadicHeightMean,intervalIntegral.integral_comp_neg,neg_neg,h₁,h₂]
  ring

lemma height_translation_window {T u Y t : ℝ} (h : 1+2*T+|u| ≤ Y)
    (ht : t ∈ Set.Icc (-2*T) (2*T)) : 1+|t+u| ≤ Y := by
  have hta : |t| ≤ 2*T := abs_le.mpr ⟨by linarith [ht.1],ht.2⟩
  linarith [abs_add_le t u]

end CubicFirstMoment

end

end OAI
