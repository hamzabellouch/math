import Mathlib
import OAI.Probability.SKSupport.Diffusion.DiffusionStability

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open Heat
variable {Ω : Type*} [MeasurableSpace Ω]

def positiveGradientErrors (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time) (n : ℕ) : Set ℝ :=
  Set.range (fun p : ℝ × ℝ => |deriv (positiveValue γ n (stripClamp T p.1)) p.2-compactGradient W γ T p.1 p.2|)

def positiveGradientError (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time) (n : ℕ) : ℝ :=
  sSup (positiveGradientErrors W γ T n)

lemma positiveGradientErrors_bddAbove (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time) (n : ℕ) :
    BddAbove (positiveGradientErrors W γ T n) := by
  obtain ⟨C,hC,hb⟩ := positiveValue_uniform_derivative_bounds γ T.property.1 T.property.2 0
  refine ⟨C+1,?_⟩
  rintro z ⟨p,rfl⟩
  have hh := hb n (stripClamp T p.1) (stripClamp_mem T.property.1 p.1) p.2
  simp only [Nat.zero_add,iteratedDeriv_one] at hh
  exact (abs_sub _ _).trans (add_le_add hh (compactGradient_bound W γ T.property.1 T.property.2 p.1 p.2))

lemma positiveGradientError_nonneg (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time) (n : ℕ) :
    0 ≤ positiveGradientError W γ T n := by
  exact (abs_nonneg _).trans (le_csSup (positiveGradientErrors_bddAbove W γ T n) ⟨((0:ℝ),(0:ℝ)),rfl⟩)

lemma positiveGradientError_bound (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time) (n : ℕ)
    {s : ℝ} (hs : s ∈ Icc (0:ℝ) T) (x : ℝ) :
    |deriv (positiveValue γ n s) x-gradient W γ s x| ≤ positiveGradientError W γ T n := by
  have hh := le_csSup (positiveGradientErrors_bddAbove W γ T n)
    (show |deriv (positiveValue γ n (stripClamp T s)) x-compactGradient W γ T s x| ∈
      positiveGradientErrors W γ T n from ⟨(s,x),rfl⟩)
  simpa only [compactGradient,stripClamp_eq hs,positiveGradientError] using hh

lemma positiveGradientError_limit (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time) :
    Tendsto (positiveGradientError W γ T) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hu := positiveValue_derivative_uniform W γ T.property.1 T.property.2 1
  rw [Metric.tendstoUniformlyOn_iff] at hu
  filter_upwards [hu (ε/2) (by linarith)] with n hn
  have he : positiveGradientError W γ T n ≤ ε/2 := by
    apply csSup_le (Set.range_nonempty _)
    rintro z ⟨p,rfl⟩
    have hh := hn (stripClamp T p.1,p.2) ⟨stripClamp_mem T.property.1 p.1,mem_univ _⟩
    simpa only [iteratedDeriv_one,Real.dist_eq,compactGradient,gradient,abs_sub_comm] using hh.le
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (positiveGradientError_nonneg W γ T n)]
  linarith

lemma positivePath_uniform_error (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ t : ℝ≥0, (t:ℝ) ≤ T → ∀ ξ,
      |positivePath W γ n t ξ-diffusion W γ t ξ| < ε := by
  let E (n : ℕ) := 2*(positiveCoeffError γ n+γ.val T*(T:ℝ)*positiveGradientError W γ T n)*
    Real.exp ((stripDrift W γ T).rate*T)
  have hE : Tendsto E atTop (𝓝 0) := by
    have hh := (positiveCoeffError_limit γ).add
      (tendsto_const_nhds.mul (positiveGradientError_limit W γ T) (a := γ.val T*(T:ℝ)))
    simpa only [E,mul_zero,zero_add,zero_mul] using
      (tendsto_const_nhds.mul hh (a := (2:ℝ))).mul_const (Real.exp ((stripDrift W γ T).rate*T))
  intro ε hε
  filter_upwards [hE.eventually (gt_mem_nhds hε)] with n hn t ht ξ
  exact (positivePath_error W γ T n (positiveGradientError_nonneg W γ T n)
    (fun s hs x => positiveGradientError_bound W γ T n hs x) t ht ξ).trans_lt hn

end ZeroTemperatureSK

end
end

end OAI
