import Mathlib
import OAI.Combinatorics.KMedian.Probability.FiniteLaws

namespace OAI

section Inline_PCPProjectionNorm

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace MixedNorm
variable {V T : Type} [Fintype V] [Fintype T]

noncomputable def sq (f : V → T → ℝ) : ℝ := 𝔼 v, ∑ t, f v t ^ 2
noncomputable def inner (f g : V → T → ℝ) : ℝ := 𝔼 v, ∑ t, f v t*g v t
noncomputable def norm (f : V → T → ℝ) : ℝ := Real.sqrt (sq f)
lemma sq_nonneg (f : V → T → ℝ) : 0 ≤ sq f :=
  expect_nonneg (fun _ _ => sum_nonneg (fun _ _ => _root_.sq_nonneg _))
lemma norm_nonneg (f : V → T → ℝ) : 0 ≤ norm f := Real.sqrt_nonneg _
lemma norm_sq (f : V → T → ℝ) : norm f ^ 2=sq f := Real.sq_sqrt (sq_nonneg f)

variable [Nonempty V]

lemma inner_sq_le (f g : V → T → ℝ) : inner f g ^ 2 ≤ sq f*sq g := by
  let ff : V × T → ℝ := fun p => f p.1 p.2
  let gg : V × T → ℝ := fun p => g p.1 p.2
  have h := sum_mul_sq_le_sq_mul_sq (s := (univ : Finset (V × T))) ff gg
  simp only [Fintype.sum_prod_type] at h
  unfold inner sq
  rw [Fintype.expect_eq_sum_div_card,Fintype.expect_eq_sum_div_card,Fintype.expect_eq_sum_div_card]
  have hn : 0 < (Fintype.card V:ℝ) := by positivity
  rw [div_pow,div_mul_div_comm]
  simpa only [ff,gg,pow_two] using (div_le_div_iff_of_pos_right (sq_pos_of_pos hn)).mpr h

lemma inner_le_norm (f g : V → T → ℝ) : inner f g ≤ norm f*norm g := by
  have h := inner_sq_le f g
  rw [← norm_sq f,← norm_sq g,← mul_pow] at h
  have hnn := mul_nonneg (norm_nonneg f) (norm_nonneg g)
  nlinarith

omit [Nonempty V] in
lemma sq_add (f g : V → T → ℝ) :
    sq (fun v t => f v t+g v t)=sq f+sq g+2*inner f g := by
  have he (v : V) (t : T) : (f v t+g v t)^2 =
      f v t^2+g v t^2+2*(f v t*g v t) := by ring
  unfold sq inner
  simp_rw [he,sum_add_distrib,← mul_sum,expect_add_distrib,← mul_expect]

lemma norm_add (f g : V → T → ℝ) :
    norm (fun v t => f v t+g v t) ≤ norm f+norm g := by
  have h := inner_le_norm f g
  have he := norm_sq (fun v t => f v t+g v t)
  rw [sq_add,← norm_sq f,← norm_sq g] at he
  nlinarith [norm_nonneg f,norm_nonneg g,norm_nonneg (fun v t => f v t+g v t)]

omit [Nonempty V] in
lemma norm_le_of_sq {f : V → T → ℝ} {b : ℝ} (hb : 0 ≤ b) (h : sq f≤b^2) :
    norm f≤b := by
  rw [← norm_sq] at h
  nlinarith [norm_nonneg f]

lemma difference_bound (f g : V → T → ℝ) : norm f ≤ norm g+norm (fun v t => f v t-g v t) := by
  have h := norm_add g (fun v t => f v t-g v t)
  simpa only [add_sub_cancel] using h

end MixedNorm
end MetricKMedian.PCP

end Inline_PCPProjectionNorm

end OAI
