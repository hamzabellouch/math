import Mathlib
import OAI.Probability.SKGap.Localization.Magnetization
import OAI.Probability.SKGap.Localization.Invert

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
namespace SKGapCutoff

lemma gap_le_eigenrate {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    {γ rate : ℝ} (hγ : HasGap J γ) (f : Observables n)
    (hc : gibbsExpectation J f = 0)
    (he : ∀ x, generator J f x = -rate * f x)
    (x : Spin n) (hx : f x ≠ 0) : γ ≤ rate := by
  have hv : 0 < gibbsVariance J f := by
    rw [gibbsVariance, hc]
    simp only [sub_zero, gibbsExpectation]
    exact Finset.sum_pos' (fun y _ => mul_nonneg (le_of_lt (gibbs_pos J y)) (sq_nonneg _))
      ⟨x, Finset.mem_univ _, mul_pos (gibbs_pos J x) (sq_pos_of_ne_zero hx)⟩
  have hd : dirichlet J f f = rate * gibbsVariance J f := by
    rw [← gibbs_dirichlet J hJ hdiag, gibbsVariance, hc]
    simp only [he, sub_zero, neg_mul, neg_neg]
    have hm (y : Spin n) : f y * (rate * f y) = rate * (f y) ^ 2 := by ring
    simp_rw [hm]
    exact gibbsExpectation_mul_const J rate (fun y => f y ^ 2)
  have h := hγ f
  rw [hd] at h
  exact le_of_mul_le_mul_right h hv

def pairInteraction (a : ℝ) : Interaction 2 := fun i j => if i = j then 0 else a

lemma pairInteraction_symm (a : ℝ) : ∀ i j, pairInteraction a i j = pairInteraction a j i := by
  intro i j
  simp only [pairInteraction, eq_comm]

lemma pairInteraction_diag (a : ℝ) : ∀ i, pairInteraction a i i = 0 := by
  intro i
  simp [pairInteraction]

lemma tanh_mul_spin {n : ℕ} (a : ℝ) (x : Spin n) (i : Fin n) :
    Real.tanh (a * spin x i) = Real.tanh a * spin x i := by
  cases h : x i <;> simp [spin, h, Real.tanh_neg]

lemma pair_field_zero (a : ℝ) (x : Spin 2) : field (pairInteraction a) x 0 = a * spin x 1 := by
  simp [field, Fin.sum_univ_two, pairInteraction]

lemma pair_field_one (a : ℝ) (x : Spin 2) : field (pairInteraction a) x 1 = a * spin x 0 := by
  simp [field, Fin.sum_univ_two, pairInteraction]

lemma pair_magnetization_eigen (a : ℝ) (x : Spin 2) :
    generator (pairInteraction a) magnetization x = -(1 - Real.tanh a) * magnetization x := by
  simp only [generator, halfDiff_magnetization, mul_one, Fin.sum_univ_two,
    mean, pair_field_zero, pair_field_one, tanh_mul_spin, magnetization]
  ring

lemma magnetization_centered {n : ℕ} (J : Interaction n) :
    gibbsExpectation J magnetization = 0 := by
  change gibbsExpectation J (fun x => ∑ i, spin x i) = 0
  rw [gibbsExpectation_sum]
  simp only [gibbs_spin_centered, Finset.sum_const_zero]

lemma pair_gap_upper (a : ℝ) {γ : ℝ} (hγ : HasGap (pairInteraction a) γ) :
    γ ≤ 1 - Real.tanh a := by
  apply gap_le_eigenrate (pairInteraction a) (pairInteraction_symm a) (pairInteraction_diag a)
    hγ magnetization (magnetization_centered _) (pair_magnetization_eigen a) (plusSpin 2)
  norm_num

theorem no_all_interaction_gap : ¬ ∃ γ : ℝ, 0 < γ ∧
    ∀ J : Interaction 2, (∀ i j, J i j = J j i) → (∀ i, J i i = 0) → HasGap J γ := by
  rintro ⟨γ, hγ, h⟩
  let δ := min γ 1 / 2
  have hδ : 0 < δ := half_pos (lt_min hγ (by norm_num))
  have hδγ : δ < γ := by
    dsimp only [δ]
    have hm := min_le_left γ 1
    linarith
  have hδ1 : δ ≤ 1 / 2 := div_le_div_of_nonneg_right (min_le_right γ 1) (by norm_num)
  have hr : 1 - δ ∈ Set.Ioo (-1 : ℝ) 1 := by constructor <;> linarith
  have hg := pair_gap_upper (Real.artanh (1 - δ))
    (h _ (pairInteraction_symm _) (pairInteraction_diag _))
  rw [Real.tanh_artanh hr] at hg
  linarith

end SKGapCutoff

open scoped BigOperators

end

end OAI
