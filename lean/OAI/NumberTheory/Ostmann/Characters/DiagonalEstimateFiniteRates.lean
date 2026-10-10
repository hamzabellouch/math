import Mathlib

namespace OAI

noncomputable section
namespace Ostmann.Characters.DiagonalEstimate

theorem exists_positive_uniform_rate {ι : Type*} [Finite ι]
    (f : ι → ℝ) (hf : ∀ i, 0 < f i) : ∃ r > 0, ∀ i, r ≤ f i := by
  classical
  let := Fintype.ofFinite ι
  cases isEmpty_or_nonempty ι with
  | inl h =>
    let := h
    exact ⟨1,by norm_num,fun i=>isEmptyElim i⟩
  | inr h =>
    let := h
    refine ⟨Finset.univ.inf' Finset.univ_nonempty f,?_,?_⟩
    · exact (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun i _=>hf i)
    · intro i
      exact Finset.inf'_le f (Finset.mem_univ i)

theorem exists_positive_uniform_rate_le_one {ι : Type*} [Finite ι]
    (f : ι → ℝ) (hf : ∀ i, 0 < f i) : ∃ r > 0, r ≤ 1 ∧ ∀ i, r ≤ f i := by
  obtain ⟨r,hr,hf'⟩ := exists_positive_uniform_rate f hf
  refine ⟨min r 1,lt_min hr (by norm_num),min_le_right _ _,?_⟩
  intro i
  exact (min_le_left _ _).trans (hf' i)

theorem exp_quadratic_decay_mono {K₁ K₂ c₁ c₂ α₁ α₂ L : ℝ}
    (hL : 0 ≤ L) (hK : K₁ ≤ K₂) (hc₀ : 0 ≤ c₂)
    (hc : c₂ ≤ c₁) (hα : α₂ ≤ α₁) :
    Real.exp (K₁*L^2-c₁*Real.exp (α₁*L)) ≤
      Real.exp (K₂*L^2-c₂*Real.exp (α₂*L)) := by
  apply Real.exp_le_exp.mpr
  apply sub_le_sub (mul_le_mul_of_nonneg_right hK (sq_nonneg L))
  exact mul_le_mul hc (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hα hL))
    (Real.exp_pos _).le (hc₀.trans hc)

end Ostmann.Characters.DiagonalEstimate

end

end OAI
