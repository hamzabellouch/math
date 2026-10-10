import Mathlib
import OAI.Combinatorics.KMedian.Probability.FiniteClipping

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
variable {T Ω : Type*} [Fintype T] [Fintype Ω]

theorem rescaling_total_noise (μ : FiniteLaw Ω) (a p : T → ℝ)
    (p' : Ω → T → ℝ) {p₀ A : ℝ} (hp₀ : 0 < p₀)
    (ha : ∀ t, 0 ≤ a t) (has : ∑ t, a t ≤ 1) (hp : ∀ t, p₀ ≤ p t)
    (hA : 0 ≤ A) (hdev : ∀ t, μ.expect (fun ω => |p' ω t-p t|) ≤ A) :
    μ.expect (fun ω => |(∑ t, a t*p' ω t/p t)-(∑ t, a t)|) ≤ A/p₀ := by
  have hpp : ∀ t, 0 < p t := fun t => hp₀.trans_le (hp t)
  have hpoint : ∀ ω, |(∑ t, a t*p' ω t/p t)-(∑ t, a t)| ≤
      ∑ t, (a t/p t)*|p' ω t-p t| := by
    intro ω
    have he : (∑ t, a t*p' ω t/p t)-(∑ t, a t)=∑ t, (a t/p t)*(p' ω t-p t) := by
      rw [← sum_sub_distrib]
      apply sum_congr rfl
      intro t _
      field_simp [(hpp t).ne']
    rw [he]
    apply (abs_sum_le_sum_abs _ _).trans_eq
    apply sum_congr rfl
    intro t _
    rw [abs_mul,abs_of_nonneg (div_nonneg (ha t) (hpp t).le)]
  have he := μ.expect_mono hpoint
  rw [FiniteLaw.expect_sum] at he
  simp only [FiniteLaw.expect_mul] at he
  have hs : (∑ t, (a t/p t)*μ.expect (fun ω => |p' ω t-p t|)) ≤ (∑ t, a t)*(A/p₀) := by
    rw [sum_mul]
    apply sum_le_sum
    intro t _
    calc
      _ ≤ (a t/p t)*A := mul_le_mul_of_nonneg_left (hdev t) (div_nonneg (ha t) (hpp t).le)
      _ ≤ (a t/p₀)*A := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (ha t) hp₀ (hp t)) hA
      _ = _ := by ring
  exact (he.trans hs).trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right has (div_nonneg hA hp₀.le))

theorem clipped_bundle_noise (μ : FiniteLaw Ω) (Z : Ω → ℝ) {c γ g : ℝ}
    (hc : 0 ≤ c) (hc1 : c ≤ 1/2) (hγ : 0 ≤ γ) (hg : 0 ≤ g)
    (hm : μ.expect Z=(1+γ)*c) (hv : μ.variance Z ≤ g*(1+γ)*c) :
    μ.expect (fun ω => |(1-min (Z ω) (1/2))-(1-c)|) ≤ γ+Real.sqrt (g*(1+γ)) := by
  have he := FiniteLaw.rescaling_noise μ Z hc hc1 hγ hg hm hv
  have hpoint : ∀ ω, (1-min (Z ω) (1/2))-(1-c)=c-min (Z ω) (1/2) := by intro ω; ring
  simp_rw [hpoint]
  apply he.trans
  apply add_le_add
  · exact (mul_le_mul_of_nonneg_left (show c ≤ 1 by linarith only [hc1]) hγ).trans_eq (mul_one _)
  · exact Real.sqrt_le_sqrt ((mul_le_mul_of_nonneg_left (show c ≤ 1 by linarith only [hc1])
      (mul_nonneg hg (by linarith only [hγ]))).trans_eq (mul_one _))

theorem rescaled_mass_bound (a p p' : T → ℝ) {p₀ : ℝ} (hp₀ : 0 < p₀)
    (ha : ∀ t, 0 ≤ a t) (has : ∑ t, a t ≤ 1) (hp : ∀ t, p₀ ≤ p t)
    (hp' : ∀ t, p' t ≤ 1) : (∑ t, a t*p' t/p t) ≤ 1/p₀ := by
  calc
    _ ≤ ∑ t, a t/p₀ := by
      apply sum_le_sum
      intro t _
      calc
        a t*p' t/p t ≤ a t/p t := div_le_div_of_nonneg_right
          ((mul_le_mul_of_nonneg_left (hp' t) (ha t)).trans_eq (mul_one _)) (hp₀.trans_le (hp t)).le
        _ ≤ a t/p₀ := div_le_div_of_nonneg_left (ha t) hp₀ (hp t)
    _ = (∑ t, a t)/p₀ := (sum_div _ _ _).symm
    _ ≤ 1/p₀ := div_le_div_of_nonneg_right has hp₀.le

end MetricKMedian.Preparation
end
end

end OAI
