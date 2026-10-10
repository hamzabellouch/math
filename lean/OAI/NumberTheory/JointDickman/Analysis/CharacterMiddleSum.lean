import OAI.NumberTheory.JointDickman.Analysis.DyadicDirichletSum

namespace OAI

/-! # Uniform control of the middle part of a character Dirichlet sum -/
namespace JointDickman
open Complex Filter Finset
open scoped Topology

lemma int_Ioc_eq_Icc_succ (a b : ℤ) : Ioc a b = Icc (a+1) b := by
  ext n
  simp only [mem_Ioc, mem_Icc]
  omega

theorem character_middle_sum_bound (B : ℝ) (hB : 1/2 ≤ B) :
    ∃ A δ U₀ : ℝ, 0 < A ∧ 0 < δ ∧ 1 ≤ U₀ ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
        (σ t : ℝ) (N : ℤ) (K : ℕ),
        U₀ ≤ (N:ℝ) → 1 ≤ σ →
        ((2:ℝ)^K*(N:ℝ))^(1/2:ℝ) ≤ |t/(2*Real.pi)| →
        |t/(2*Real.pi)| ≤ (N:ℝ)^B →
        ‖∑ n ∈ Ioc N ((2:ℤ)^K*N), χ (n:ZMod q)*(n:ℂ)^(-((σ:ℂ)+(t:ℂ)*I))‖ ≤
          ((q:ℝ)*A)*(N:ℝ)^(-δ)/(1-(2:ℝ)^(-δ)) := by
  obtain ⟨A,δ,hA,hδ,hh⟩ := character_dyadic_sum_uniform B hB
  obtain ⟨U₀,hU₀⟩ := eventually_atTop.mp hh
  refine ⟨A,δ,max 1 U₀,hA,hδ,le_max_left _ _,?_⟩
  intro q _ χ σ t N K hN hσ hlo hhi
  have hN1 : (1:ℝ) ≤ N := (le_max_left _ _).trans hN
  have hN0 : 0 < N := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hN1)
  apply norm_dyadic_sum_bound _ hN0 (by positivity) hδ
  intro j hj
  have hNj : (N:ℝ) ≤ (2:ℝ)^j*(N:ℝ) := by
    nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := j)]
  have hUj : U₀ ≤ (2:ℝ)^j*(N:ℝ) := ((le_max_right _ _).trans hN).trans hNj
  have hpow : (2:ℝ)^j*(N:ℝ) ≤ (2:ℝ)^K*(N:ℝ) :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj.le) (by linarith)
  rw [int_Ioc_eq_Icc_succ]
  have hc := hU₀ _ hUj q χ σ t (((2:ℤ)^j*N)+1) ((2:ℤ)^(j+1)*N) hσ
    ((Real.rpow_le_rpow (by positivity) hpow (by norm_num)).trans hlo)
    (hhi.trans (Real.rpow_le_rpow (by linarith) hNj (by linarith)))
    (by push_cast; linarith)
    (by push_cast; rw [pow_succ]; ring_nf; exact le_rfl)
  simpa only [mul_assoc] using hc

end JointDickman

end OAI
