import Mathlib

namespace OAI

section

open MeasureTheory Set Filter
open scoped Topology
namespace SKValue

lemma strip_integral_limit {T a b Γ A B : ℝ}
    {c : ℕ → ℝ → ℝ} {γ : ℝ → ℝ} {f g : ℕ → ℝ → ℝ} {F G : ℝ → ℝ}
    (ha : a∈Icc (0 : ℝ) T) (hb : b∈Icc (0 : ℝ) T)
    (hc : ∀ n, Measurable (c n))
    (hf : ∀ n, ContinuousOn (f n) (Icc (0 : ℝ) T))
    (hg : ∀ n, ContinuousOn (g n) (Icc (0 : ℝ) T))
    (hcb : ∀ n t, t∈Icc (0 : ℝ) T → |c n t| ≤ Γ)
    (hfb : ∀ n t, t∈Icc (0 : ℝ) T → |f n t| ≤ A)
    (hgb : ∀ n t, t∈Icc (0 : ℝ) T → |g n t| ≤ B)
    (hΓ : 0 ≤ Γ)
    (hlc : ∀ᵐ t ∂volume, t∈Icc (0 : ℝ) T → Tendsto (fun n ↦ c n t) atTop (𝓝 (γ t)))
    (hlf : ∀ t∈Icc (0 : ℝ) T, Tendsto (fun n ↦ f n t) atTop (𝓝 (F t)))
    (hlg : ∀ t∈Icc (0 : ℝ) T, Tendsto (fun n ↦ g n t) atTop (𝓝 (G t))) :
    Tendsto (fun n ↦ ∫ t in a..b, f n t+c n t*g n t) atTop
      (𝓝 (∫ t in a..b, F t+γ t*G t)) := by
  have hsub : uIoc a b⊆Icc (0 : ℝ) T := uIoc_subset_uIcc.trans (uIcc_subset_Icc ha hb)
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ ↦ A+Γ*B)
  · apply Eventually.of_forall
    intro n
    exact ((hf n).aestronglyMeasurable measurableSet_Icc |>.mono_set hsub).add
      ((hc n).aestronglyMeasurable.mul ((hg n).aestronglyMeasurable measurableSet_Icc |>.mono_set hsub))
  · apply Eventually.of_forall
    intro n
    apply Eventually.of_forall
    intro t ht
    rw [Real.norm_eq_abs]
    exact (abs_add_le _ _).trans (add_le_add (hfb n t (hsub ht)) (by
      rw [abs_mul]
      exact mul_le_mul (hcb n t (hsub ht)) (hgb n t (hsub ht)) (abs_nonneg _) hΓ))
  · exact intervalIntegrable_const
  · filter_upwards [hlc] with t hlt ht
    exact (hlf t (hsub ht)).add ((hlt (hsub ht)).mul (hlg t (hsub ht)))

end SKValue

end

end OAI
