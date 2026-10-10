import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialScalarDirichlet

namespace OAI

/-! The prescribed-potential inner amplitude, with the manuscript's pressure bound. -/

open Set
namespace DefocusingNLS

theorem exists_radial_scalar_profile_regular (p : ℕ) (hp : 2 ≤ p) (R lo : ℝ)
    (hR : 0 < R) (hlo : 0 < lo) (hSmall : lo^(p-1) ≤ (3/10 : ℝ))
    (V : ℝ → ℝ) (hV : Continuous V)
    (hVB : ∀ r ∈ Icc 0 R, V r ∈ Icc (3/10 : ℝ) (1/2)) :
    ∃ A : ℝ → ℝ, Differentiable ℝ A ∧
      (∀ r ∈ Ioo 0 R, DifferentiableAt ℝ (deriv A) r) ∧
      A R=lo ∧ HasDerivAt A 0 0 ∧
      (∀ r ∈ Icc 0 R, lo ≤ A r ∧ (A r)^(p-1) ≤ (1/2 : ℝ)) ∧
      (∀ r ∈ Ioo 0 R,
        -deriv (deriv A) r-11/r*deriv A r+(A r)^p=V r*A r) := by
  have hn : p-1 ≠ 0 := by omega
  have ht : (1/2 : ℝ) ∈ Icc ((0 : ℝ)^(p-1)) ((1 : ℝ)^(p-1)) := by
    simp only [zero_pow hn,one_pow,mem_Icc]
    norm_num
  obtain ⟨hi,hhi,hpow⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
    (continuous_id.pow (p-1)).continuousOn ht
  change hi^(p-1)=(1/2 : ℝ) at hpow
  have hlohi : lo ≤ hi := by
    by_contra! hlt
    have h := pow_le_pow_left₀ hhi.1 hlt.le (p-1)
    rw [hpow] at h
    linarith
  have hp' : p-1+1=p := by omega
  have hLower : ∀ r ∈ Icc 0 R, lo^p ≤ V r*lo := by
    intro r hr
    rw [← hp',pow_succ]
    exact mul_le_mul_of_nonneg_right (hSmall.trans (hVB r hr).1) hlo.le
  have hUpper : ∀ r ∈ Icc 0 R, V r*hi ≤ hi^p := by
    intro r hr
    rw [← hp',pow_succ,hpow]
    exact mul_le_mul_of_nonneg_right (hVB r hr).2 hhi.1
  have hVC : ∀ r ∈ Icc 0 R, ‖V r‖ ≤ (1/2 : ℝ) := by
    intro r hr
    rw [Real.norm_eq_abs,abs_of_nonneg (le_trans (by norm_num) (hVB r hr).1)]
    exact (hVB r hr).2
  obtain ⟨A,hAd,hD,hAR,hA0,hAI,hEq⟩ := exists_radial_scalar_dirichlet_regular p R lo hi (1/2)
    hR hlo.le hlohi hhi.2 (by norm_num) V hV hVC hLower hUpper
  refine ⟨A,hAd,hD,hAR,hA0,?_,hEq⟩
  intro r hr
  refine ⟨(hAI r hr).1,?_⟩
  exact (pow_le_pow_left₀ (hlo.le.trans (hAI r hr).1) (hAI r hr).2 (p-1)).trans_eq hpow

theorem exists_radial_scalar_profile (p : ℕ) (hp : 2 ≤ p) (R lo : ℝ)
    (hR : 0 < R) (hlo : 0 < lo) (hSmall : lo^(p-1) ≤ (3/10 : ℝ))
    (V : ℝ → ℝ) (hV : Continuous V)
    (hVB : ∀ r ∈ Icc 0 R, V r ∈ Icc (3/10 : ℝ) (1/2)) :
    ∃ A : ℝ → ℝ, Differentiable ℝ A ∧ A R=lo ∧ HasDerivAt A 0 0 ∧
      (∀ r ∈ Icc 0 R, lo ≤ A r ∧ (A r)^(p-1) ≤ (1/2 : ℝ)) ∧
      (∀ r ∈ Ioo 0 R,
        -deriv (deriv A) r-11/r*deriv A r+(A r)^p=V r*A r) := by
  obtain ⟨A,hA,_,hAR,hA0,hAI,hEq⟩ :=
    exists_radial_scalar_profile_regular p hp R lo hR hlo hSmall V hV hVB
  exact ⟨A,hA,hAR,hA0,hAI,hEq⟩

end DefocusingNLS

end OAI
