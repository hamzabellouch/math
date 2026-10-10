import Mathlib

namespace OAI

/-! Gaussian regularization, Fourier evolution and endpoint maximal estimates. -/


noncomputable section
open scoped BigOperators
namespace PlanarEndpoint

lemma near_sum_first {ι : Type*} [Fintype ι] (R : ι → ι → Prop)
    [DecidableRel R] (a : ι → ℝ) :
    (∑ i, ∑ j, if R i j then a i else 0) =
      ∑ i, ((Finset.univ.filter (R i)).card : ℝ) * a i := by
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_filter]
  simp

lemma symmetric_near_sum {ι : Type*} [Fintype ι] (R : ι → ι → Prop)
    [DecidableRel R] (hR : ∀ ⦃first second⦄, R first second → R second first) (a : ι → ℝ) :
    (∑ i, ∑ j, if R i j then (a i+a j)/2 else 0) =
      ∑ i, ((Finset.univ.filter (R i)).card : ℝ) * a i := by
  have he (i j : ι) : (if R i j then (a i+a j)/2 else 0) =
      ((if R i j then a i else 0)+(if R i j then a j else 0))/2 := by
    split_ifs <;> ring
  simp_rw [he, ← Finset.sum_div, Finset.sum_add_distrib]
  have hs : (∑ i, ∑ j, if R i j then a j else 0) = ∑ i, ∑ j, if R i j then a i else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [show R j i ↔ R i j from ⟨fun h => hR h, fun h => hR h⟩]
  rw [hs, near_sum_first]
  ring

lemma norm_sum_sq_le_near_far {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (G : ι → E) (R : ι → ι → Prop) [DecidableRel R]
    (hR : ∀ ⦃first second⦄, R first second → R second first)
    (m : ι → ℝ) (hm : ∀ i, 0 ≤ m i) {D B : ℝ} (hB : 0 ≤ B)
    (hdegree : ∀ i, ((Finset.univ.filter (R i)).card : ℝ) ≤ D)
    (hfar : ∀ i j, ¬R i j → ‖inner ℂ (G i) (G j)‖ ≤ B * m i * m j) :
    ‖∑ i, G i‖^2 ≤ D * (∑ i, ‖G i‖^2) + B * (∑ i, m i)^2 := by
  have hp (i j : ι) : (inner ℂ (G i) (G j)).re ≤
      (if R i j then (‖G i‖^2+‖G j‖^2)/2 else 0) + B*m i*m j := by
    have hnn : 0 ≤ B*m i*m j := mul_nonneg (mul_nonneg hB (hm i)) (hm j)
    by_cases hij : R i j
    · rw [ite_eq_left hij]
      have hc := norm_inner_le_norm (𝕜 := ℂ) (G i) (G j)
      have hr := Complex.re_le_norm (inner ℂ (G i) (G j))
      nlinarith [sq_nonneg (‖G i‖-‖G j‖)]
    · rw [ite_eq_right hij, zero_add]
      exact (Complex.re_le_norm _).trans (hfar i j hij)
  calc
    _ = ∑ i, ∑ j, (inner ℂ (G i) (G j)).re := by
      rw [← @inner_self_eq_norm_sq ℂ E _ _]
      simp only [sum_inner, inner_sum, map_sum]
      exact Finset.sum_comm
    _ ≤ ∑ i, ∑ j, ((if R i j then (‖G i‖^2+‖G j‖^2)/2 else 0) + B*m i*m j) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hp i j))
    _ = (∑ i, ((Finset.univ.filter (R i)).card : ℝ) * ‖G i‖^2) +
        B * (∑ i, m i)^2 := by
      simp_rw [Finset.sum_add_distrib]
      rw [symmetric_near_sum R hR]
      congr 1
      simp only [Finset.mul_sum, Finset.sum_mul, pow_two]
      rw [Finset.sum_comm]
      simp only [mul_assoc]
    _ ≤ _ := by
      apply add_le_add_left
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hdegree i) (sq_nonneg _)

lemma norm_sum_sq_le_near_error {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (G : ι → E) (R : ι → ι → Prop) [DecidableRel R]
    (hR : ∀ ⦃first second⦄, R first second → R second first)
    (A : ι → ι → ℝ) (hA : ∀ i j, 0 ≤ A i j) {D : ℝ}
    (hdegree : ∀ i, ((Finset.univ.filter (R i)).card : ℝ) ≤ D)
    (hfar : ∀ i j, ¬R i j → ‖inner ℂ (G i) (G j)‖ ≤ A i j) :
    ‖∑ i, G i‖^2 ≤ D * (∑ i, ‖G i‖^2) + ∑ i, ∑ j, A i j := by
  have hp (i j : ι) : (inner ℂ (G i) (G j)).re ≤
      (if R i j then (‖G i‖^2+‖G j‖^2)/2 else 0) + A i j := by
    by_cases hij : R i j
    · rw [ite_eq_left hij]
      have hc := norm_inner_le_norm (𝕜 := ℂ) (G i) (G j)
      have hr := Complex.re_le_norm (inner ℂ (G i) (G j))
      nlinarith [sq_nonneg (‖G i‖-‖G j‖), hA i j]
    · rw [ite_eq_right hij, zero_add]
      exact (Complex.re_le_norm _).trans (hfar i j hij)
  calc
    _ = ∑ i, ∑ j, (inner ℂ (G i) (G j)).re := by
      rw [← @inner_self_eq_norm_sq ℂ E _ _]
      simp only [sum_inner, inner_sum, map_sum]
      exact Finset.sum_comm
    _ ≤ ∑ i, ∑ j, ((if R i j then (‖G i‖^2+‖G j‖^2)/2 else 0) + A i j) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hp i j))
    _ = (∑ i, ((Finset.univ.filter (R i)).card : ℝ) * ‖G i‖^2) +
        ∑ i, ∑ j, A i j := by
      simp_rw [Finset.sum_add_distrib]
      rw [symmetric_near_sum R hR]
    _ ≤ _ := by
      apply add_le_add_left
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hdegree i) (sq_nonneg _)

end PlanarEndpoint
end

end OAI
