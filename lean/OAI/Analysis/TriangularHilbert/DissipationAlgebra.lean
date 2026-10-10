import OAI.Analysis.TriangularHilbert.PlaneTime

namespace OAI

section
namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped BigOperators

lemma finite_cost_dissipation (α : Three → ℝ) (hα : ∀ w, 0 ≤ α w)
    (K : Three → Three → ℝ) (Z : Three → ℝ) (hK : ∀ v w, 0 ≤ K v w)
    (hrow : ∀ v, 2*Z v ≤ ∑ w, if w = v then 0 else K v w)
    (hcol : ∀ w, (∑ v, if v = w then 0 else K v w) ≤ Real.sqrt 2 * K w w) :
    (∑ v, ((∑ w, α w)*Z v - (∑ w, α w*K v w))) ≤
      ∑ w, (-α w + Real.sqrt 2 * max 0 ((∑ v, α v)/2-α w))*K w w := by
  let S := ∑ w, α w
  have hS : 0 ≤ S := Finset.sum_nonneg (fun w _ => hα w)
  have hr v : S*Z v ≤ S/2 * ∑ w, if w = v then 0 else K v w := by
    have hh := mul_le_mul_of_nonneg_left (hrow v) (show 0 ≤ S/2 by positivity)
    nlinarith
  have hc w : (S/2-α w)*(∑ v, if v = w then 0 else K v w) ≤
      Real.sqrt 2 * max 0 (S/2-α w)*K w w := by
    have ho : 0 ≤ ∑ v, if v = w then 0 else K v w :=
      Finset.sum_nonneg (fun v _ => by split_ifs; exact le_refl 0; exact hK v w)
    calc
      _ ≤ max 0 (S/2-α w)*(∑ v, if v = w then 0 else K v w) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) ho
      _ ≤ max 0 (S/2-α w)*(Real.sqrt 2*K w w) :=
        mul_le_mul_of_nonneg_left (hcol w) (le_max_left _ _)
      _ = _ := by ring
  calc
    _ ≤ ∑ v, (S/2*(∑ w, if w = v then 0 else K v w) - (∑ w, α w*K v w)) := by
      apply Finset.sum_le_sum
      intro v _
      exact sub_le_sub_right (hr v) _
    _ = ∑ w, (-α w*K w w + (S/2-α w)*(∑ v, if v = w then 0 else K v w)) := by
      simp [Fin.sum_univ_three]
      ring
    _ ≤ ∑ w, (-α w*K w w + Real.sqrt 2 * max 0 (S/2-α w)*K w w) := by
      apply Finset.sum_le_sum
      intro w _
      exact add_le_add (le_refl _) (hc w)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w _
      dsimp [S]
      ring

lemma offdiag_sum_eq (f : Three → ℝ) (v : Three) :
    (∑ w, if w = v then 0 else f w) = f (v+1)+f (v+2) := by
  fin_cases v <;> simp [Fin.sum_univ_three, add_comm]

lemma neighbor_one_ne (v : Three) : v+1 ≠ v := by fin_cases v <;> decide
lemma neighbor_two_ne (v : Three) : v+2 ≠ v := by fin_cases v <;> decide
lemma neighbors_ne (v : Three) : v+1 ≠ v+2 := by fin_cases v <;> decide
end TriangularHilbert.Heat
end

end OAI
