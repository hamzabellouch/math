import Mathlib
import OAI.Probability.SKSupport.Model

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma taylor1_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {C : ℝ}
    (hC : ∀ x, |deriv (deriv f) x| ≤ C) (x d : ℝ) :
    |f (x+d)-f x-deriv f x*d| ≤ C/2*|d|^2 := by
  by_cases hd : d = 0
  · simp [hd]
  have hxd : x ≠ x+d := by intro h; apply hd; linarith
  obtain ⟨y,hy,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := 1) hxd hf.contDiffOn
  have h1 : iteratedDerivWithin 1 f (Set.uIcc x (x+d)) x = deriv f x := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hxd)
      (hf.of_le (by norm_num)).contDiffAt left_mem_uIcc, iteratedDeriv_one]
  simp only [taylorWithinEval_succ, taylor_within_zero_eval, h1,
    iteratedDeriv_succ] at he
  norm_num at he
  have he' : f (x+d)-f x-deriv f x*d = deriv (deriv f) y*d^2/2 := by
    calc
      _ = f (x+d)-(f x+d*deriv f x) := by ring
      _ = _ := by convert he using 1
  rw [he', abs_div, abs_mul, abs_pow]
  norm_num
  have := mul_le_mul_of_nonneg_right (hC y) (sq_nonneg d)
  nlinarith

lemma derivative_interpolation {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {A C : ℝ} (hA : ∀ x, |f x| ≤ A) (hC : ∀ x, |deriv (deriv f) x| ≤ C)
    {h : ℝ} (hh : 0 < h) (x : ℝ) :
    |deriv f x| ≤ 2*A/h+h*C/2 := by
  have ht := taylor1_bound hf hC x h
  rw [abs_of_pos hh] at ht
  have hs : |deriv f x*h| ≤ 2*A+C/2*h^2 := by
    calc
      _ = |f (x+h)-f x-(f (x+h)-f x-deriv f x*h)| := by congr 1; ring
      _ ≤ |f (x+h)-f x|+|f (x+h)-f x-deriv f x*h| := abs_sub _ _
      _ ≤ (|f (x+h)|+|f x|)+C/2*h^2 := add_le_add (abs_sub _ _) ht
      _ ≤ 2*A+C/2*h^2 := by linarith [hA (x+h),hA x]
  rw [abs_mul, abs_of_pos hh] at hs
  have he : (2*A/h+h*C/2)*h = 2*A+C/2*h^2 := by field_simp
  nlinarith

lemma tendstoUniformly_deriv_zero {ι : Type*} {l : Filter ι}
    {f : ι → ℝ → ℝ} (hf : ∀ i, ContDiff ℝ 2 (f i))
    {C : ℝ≥0} (hC : ∀ i x, |deriv (deriv (f i)) x| ≤ C)
    (hlim : TendstoUniformly f (fun _ => 0) l) :
    TendstoUniformly (fun i => deriv (f i)) (fun _ => 0) l := by
  rw [Metric.tendstoUniformly_iff] at hlim ⊢
  intro ε hε
  let h : ℝ := ε / ((C:ℝ)+1)
  have hh : 0 < h := div_pos hε (by positivity)
  have hδ : 0 < ε*h/4 := by positivity
  filter_upwards [hlim (ε*h/4) hδ] with i hi x
  have hA : ∀ y, |f i y| ≤ ε*h/4 := fun y => le_of_lt (by
    simpa only [Real.dist_eq, sub_zero, abs_sub_comm] using hi y)
  have hd := derivative_interpolation (hf i) hA (hC i) hh x
  have hc : h*(C:ℝ) < ε := by
    dsimp [h]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (show (0:ℝ)<C+1 by positivity)).mpr
    nlinarith
  have he : 2*(ε*h/4)/h = ε/2 := by field_simp; ring
  rw [he] at hd
  simpa only [Real.dist_eq, sub_zero, abs_sub_comm] using (show |deriv (f i) x| < ε by linarith)

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI
