import Mathlib
import OAI.Combinatorics.KMedian.Probability.SumLaws

namespace OAI

namespace MetricKMedian.FiniteLaw
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

noncomputable def variance (μ : FiniteLaw Ω) (f : Ω → ℝ) : ℝ :=
  μ.expect (fun ω => (f ω-μ.expect f)^2)

omit [Fintype Ξ] in
theorem variance_nonneg (μ : FiniteLaw Ω) (f : Ω → ℝ) : 0 ≤ μ.variance f :=
  μ.expect_nonneg (fun _ => sq_nonneg _)

omit [Fintype Ξ] in
theorem variance_eq (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    μ.variance f=μ.expect (fun ω => (f ω)^2)-(μ.expect f)^2 := by
  unfold variance
  have hp : ∀ ω, (f ω-μ.expect f)^2=(f ω)^2-2*μ.expect f*f ω+(μ.expect f)^2 := by
    intro ω; ring
  simp_rw [hp, expect_add, expect_sub, expect_mul, expect_const]
  ring

omit [Fintype Ξ] in
theorem sq_expect_le_expect_sq (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    (μ.expect f)^2 ≤ μ.expect (fun ω => (f ω)^2) := by
  have hv := μ.variance_nonneg f
  rw [variance_eq] at hv
  linarith only [hv]

omit [Fintype Ξ] in
theorem variance_const (μ : FiniteLaw Ω) (c : ℝ) : μ.variance (fun _ => c)=0 := by
  rw [variance_eq, expect_const, expect_const, sub_self]

omit [Fintype Ξ] in
theorem expect_abs_le (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    |μ.expect f| ≤ μ.expect (fun ω => |f ω|) := by
  unfold expect
  calc
    _ ≤ ∑ ω, |μ.weight ω*f ω| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := Finset.sum_congr rfl (fun ω _ => by rw [abs_mul, abs_of_nonneg (μ.nonneg ω)])

theorem variance_sumMix (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (μ : FiniteLaw Ω) (ν : FiniteLaw Ξ) (f : Ω ⊕ Ξ → ℝ) :
    (sumMix θ hθ0 hθ1 μ ν).variance f =
      θ*μ.variance (fun ω => f (.inl ω))+(1-θ)*ν.variance (fun ξ => f (.inr ξ))+
      θ*(1-θ)*(μ.expect (fun ω => f (.inl ω))-ν.expect (fun ξ => f (.inr ξ)))^2 := by
  simp only [variance_eq, expect_sumMix]
  ring

omit [Fintype Ξ] in

theorem prob_le_expect_div (μ : FiniteLaw Ω) (f : Ω → ℝ) {t : ℝ}
    (hf : ∀ ω, 0 ≤ f ω) (ht : 0 < t) :
    μ.prob (fun ω => t ≤ f ω) ≤ μ.expect f/t := by
  classical
  apply (le_div_iff₀ ht).mpr
  unfold prob
  rw [← expect_mul_right]
  apply μ.expect_mono
  intro ω
  split_ifs with h
  · simpa only [one_mul] using h
  · simpa only [zero_mul] using hf ω

omit [Fintype Ξ] in
theorem chebyshev (μ : FiniteLaw Ω) (f : Ω → ℝ) {t : ℝ} (ht : 0 < t) :
    μ.prob (fun ω => t ≤ |f ω-μ.expect f|) ≤ μ.variance f/t^2 := by
  classical
  have he : ∀ ω, (t ≤ |f ω-μ.expect f|) ↔ t^2 ≤ (f ω-μ.expect f)^2 := by
    intro ω
    exact (sq_le_sq₀ ht.le (abs_nonneg _)).symm.trans (by rw [sq_abs])
  rw [μ.prob_congr he]
  exact μ.prob_le_expect_div (fun ω => (f ω-μ.expect f)^2) (fun _ => sq_nonneg _) (sq_pos_of_pos ht)

omit [Fintype Ξ] in
                                                                                 
theorem prob_positive_le (μ : FiniteLaw Ω) (f : Ω → ℝ) {t : ℝ} (ht : 0 < t)
    (hmean : μ.expect f ≤ -t) :
    μ.prob (fun ω => 0 < f ω) ≤ μ.variance f/t^2 := by
  classical
  apply (μ.prob_mono (E := fun ω => 0 < f ω)
    (F := fun ω => t ≤ |f ω-μ.expect f|) ?_).trans (μ.chebyshev f ht)
  intro ω hω
  have hh : t ≤ f ω-μ.expect f := by linarith only [hω, hmean]
  exact hh.trans (le_abs_self _)

end MetricKMedian.FiniteLaw

end OAI
