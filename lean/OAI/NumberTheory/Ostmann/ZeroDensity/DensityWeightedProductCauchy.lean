import OAI.NumberTheory.Ostmann.ZeroDensity.DensityWeightedCauchy

namespace OAI

/-! # Weighted product Cauchy inequalities for the zero detector -/

namespace Ostmann

open MeasureTheory
open scoped BigOperators

 theorem density_product_cauchy (w f g : ℝ → ℝ)
    (hw : ∀ x, 0 ≤ w x)
    (hff : Integrable (fun x => w x * f x ^ 2))
    (hgg : Integrable (fun x => w x * g x ^ 2))
    (hfg : Integrable (fun x => w x * f x * g x)) :
    (∫ x, w x * f x * g x) ^ 2 ≤
      (∫ x, w x * f x ^ 2) * ∫ x, w x * g x ^ 2 := by
  let A := ∫ x, w x * f x ^ 2
  let B := ∫ x, w x * f x * g x
  let D := ∫ x, w x * g x ^ 2
  have hA : 0 ≤ A := integral_nonneg (fun x => mul_nonneg (hw x) (sq_nonneg _))
  have hq (t : ℝ) : 0 ≤ D - 2 * t * B + t ^ 2 * A := by
    have he : (fun x => w x * (g x - t * f x) ^ 2) =
        (fun x => (w x * g x ^ 2 - (2 * t) * (w x * f x * g x)) + t ^ 2 * (w x * f x ^ 2)) := by
      funext x
      ring
    have hh := integral_add (hgg.sub (hfg.const_mul (2 * t))) (hff.const_mul (t ^ 2))
    have hs := integral_sub hgg (hfg.const_mul (2 * t))
    simp only [Pi.sub_apply] at hh hs
    have hn : 0 ≤ ∫ x, w x * (g x - t * f x) ^ 2 :=
      integral_nonneg (fun x => mul_nonneg (hw x) (sq_nonneg _))
    rw [he, hh, hs, integral_const_mul, integral_const_mul] at hn
    exact hn
  change B ^ 2 ≤ A * D
  by_cases ha : 0 < A
  · have ht : (B / A) * A = B := div_mul_cancel₀ B ha.ne'
    have hh := hq (B / A)
    have hm := mul_nonneg ha.le hh
    have hs := congrArg (fun x : ℝ => x ^ 2) ht
    nlinarith
  · have ha0 : A = 0 := le_antisymm (le_of_not_gt ha) hA
    by_cases hb : B = 0
    · simp [ha0, hb]
    · have ht : ((D + 1) / (2 * B)) * (2 * B) = D + 1 :=
        div_mul_cancel₀ _ (mul_ne_zero (by norm_num) hb)
      have hh := hq ((D + 1) / (2 * B))
      rw [ha0, mul_zero, add_zero] at hh
      nlinarith

 theorem density_finite_product_cauchy {ι : Type*} (S : Finset ι)
    (w f g : ι → ℝ → ℝ) (hw : ∀ i ∈ S, ∀ x, 0 ≤ w i x)
    (hff : ∀ i ∈ S, Integrable (fun x => w i x * f i x ^ 2))
    (hgg : ∀ i ∈ S, Integrable (fun x => w i x * g i x ^ 2))
    (hfg : ∀ i ∈ S, Integrable (fun x => w i x * f i x * g i x)) :
    (∑ i ∈ S, ∫ x, w i x * f i x * g i x) ^ 2 ≤
      (∑ i ∈ S, ∫ x, w i x * f i x ^ 2) *
        ∑ i ∈ S, ∫ x, w i x * g i x ^ 2 := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul S
    (fun i hi => integral_nonneg (fun x => mul_nonneg (hw i hi x) (sq_nonneg _)))
    (fun i hi => integral_nonneg (fun x => mul_nonneg (hw i hi x) (sq_nonneg _)))
  intro i hi
  exact density_product_cauchy (w i) (f i) (g i) (hw i hi) (hff i hi) (hgg i hi) (hfg i hi)

 theorem density_finite_product_fourth {ι : Type*} (S : Finset ι)
    (w f g : ι → ℝ → ℝ) (hw : ∀ i ∈ S, ∀ x, 0 ≤ w i x)
    (h0 : ∀ i ∈ S, Integrable (w i))
    (h2 : ∀ i ∈ S, Integrable (fun x => w i x * f i x ^ 2))
    (h4 : ∀ i ∈ S, Integrable (fun x => w i x * f i x ^ 4))
    (hg : ∀ i ∈ S, Integrable (fun x => w i x * g i x ^ 2))
    (hfg : ∀ i ∈ S, Integrable (fun x => w i x * f i x * g i x)) :
    (∑ i ∈ S, ∫ x, w i x * f i x * g i x) ^ 4 ≤
      (∑ i ∈ S, ∫ x, w i x) * (∑ i ∈ S, ∫ x, w i x * f i x ^ 4) *
        (∑ i ∈ S, ∫ x, w i x * g i x ^ 2) ^ 2 := by
  have hfirst := density_finite_product_cauchy S w f g hw h2 hg hfg
  have hsecond := density_finite_product_cauchy S w (fun _ _ => 1) (fun i x => f i x ^ 2) hw
    (fun i hi => by simpa using h0 i hi)
    (fun i hi => by simpa only [← pow_mul] using h4 i hi)
    (fun i hi => by simpa using h2 i hi)
  simp only [one_pow, mul_one, ← pow_mul] at hsecond
  calc
    _ = ((∑ i ∈ S, ∫ x, w i x * f i x * g i x) ^ 2) ^ 2 := by ring
    _ ≤ ((∑ i ∈ S, ∫ x, w i x * f i x ^ 2) *
        (∑ i ∈ S, ∫ x, w i x * g i x ^ 2)) ^ 2 :=
      pow_le_pow_left₀ (sq_nonneg _) hfirst 2
    _ = (∑ i ∈ S, ∫ x, w i x * f i x ^ 2) ^ 2 *
        (∑ i ∈ S, ∫ x, w i x * g i x ^ 2) ^ 2 := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right hsecond (sq_nonneg _)

end Ostmann

end OAI
