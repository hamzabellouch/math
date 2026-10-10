import Mathlib

namespace OAI

noncomputable section
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
namespace YauCounterexamples

theorem radial_transition_positive (m C D t η T : ℝ)
    (hm : 0 < m) (ht : 0 ≤ t) (hη : η ≤ m/4)
    (hD : C^2 ≤ (D-C)*m)
    (htrace : m-C*t-C*Real.sqrt t-η+D*t ≤ T) : m/2 ≤ T := by
  have hs := Real.sq_sqrt ht
  have hn := sq_nonneg (m-2*C*Real.sqrt t)
  have hd := mul_le_mul_of_nonneg_right hD ht
  have hsmall : m*(C*Real.sqrt t) ≤ m^2/4+C^2*t := by
    nlinarith only [hs,hn]
  have hbound : m/2 ≤ m-C*t-C*Real.sqrt t-η+D*t := by
    apply (mul_le_mul_iff_right₀ hm).mp
    nlinarith only [hsmall,hd,mul_le_mul_of_nonneg_right hη hm.le]
  exact hbound.trans htrace

theorem radial_transition_uniform {X : Type*} (m C k : ℝ)
    (hm : 0 < m) (hk : 0 < k) (t T : ℕ → X → ℝ)
    (ht : ∀ N x, 0 ≤ t N x)
    (htrace : ∀ᶠ N : ℕ in atTop, ∀ x,
      m-C*t N x-C*Real.sqrt (t N x)-C/(N:ℝ)+k*(N:ℝ)*t N x ≤ T N x) :
    ∀ᶠ N : ℕ in atTop, ∀ x, m/2 ≤ T N x := by
  have hnat : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun N : ℕ => C/(N:ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,Function.comp_apply,mul_zero] using
      tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hnat)
  have hη := hinv.eventually (Iio_mem_nhds (by linarith : (0:ℝ) < m/4))
  have hlarge : ∀ᶠ N : ℕ in atTop, (C+C^2/m)/k ≤ (N:ℝ) :=
    hnat.eventually (eventually_ge_atTop _)
  filter_upwards [htrace,hη,hlarge] with N hN hηN hLN x
  have h1 : C+C^2/m ≤ k*(N:ℝ) := by
    have hh := (div_le_iff₀ hk).mp hLN
    nlinarith only [hh]
  have h2 : C^2 ≤ (k*(N:ℝ)-C)*m := by
    have hdiv : C^2/m ≤ k*(N:ℝ)-C := by linarith
    exact (div_le_iff₀ hm).mp hdiv
  exact radial_transition_positive m C (k*(N:ℝ)) (t N x) (C/(N:ℝ)) (T N x)
    hm (ht N x) hηN.le h2 (hN x)
end YauCounterexamples

end

end OAI
