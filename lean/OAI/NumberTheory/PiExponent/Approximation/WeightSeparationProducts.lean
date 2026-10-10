import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Basic.Real.Basic

namespace OAI

namespace PiExponent

theorem product_dominance_of_lower_indices
    (x : ℕ → ℝ) (D : ℝ) (hx : ∀ j, 1 ≤ x j) (hD : 0 < D)
    (A B : Finset ℕ) (i : ℕ) (hiA : i ∈ A)
    (hB : ∀ j ∈ B, j < i)
    (hgrowth : D * (∏ j ∈ Finset.range i, x j) < x i) :
    D * (∏ j ∈ B, x j) < ∏ j ∈ A, x j := by
  have hxnonneg : ∀ j, 0 ≤ x j := fun j => le_trans zero_le_one (hx j)
  have hsub : B ⊆ Finset.range i := by
    intro j hj
    exact Finset.mem_range.mpr (hB j hj)
  have hprodB : (∏ j ∈ B, x j) ≤ ∏ j ∈ Finset.range i, x j :=
    Finset.prod_le_prod_of_subset_of_one_le₀ hsub
      (fun j _ => hxnonneg j) (fun j _ _ => hx j)
  have hprodA : x i ≤ ∏ j ∈ A, x j := by
    have hsubA : ({i} : Finset ℕ) ⊆ A := Finset.singleton_subset_iff.mpr hiA
    simpa only [Finset.prod_singleton] using
      (Finset.prod_le_prod_of_subset_of_one_le₀ hsubA
        (fun j _ => hxnonneg j) (fun j _ _ => hx j))
  exact lt_of_lt_of_le
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hprodB hD.le) hgrowth) hprodA

theorem normalized_products_separated
    (x : ℕ → ℝ) (D : ℝ) (hx : ∀ j, 1 ≤ x j) (hD : 0 < D)
    (A B : Finset ℕ) (i : ℕ) (hiA : i ∈ A) (hiB : i ∉ B)
    (hB : ∀ j ∈ B \ A, j < i)
    (hgrowth : D * (∏ j ∈ Finset.range i, x j) < x i) :
    D * (∏ j ∈ B, x j) < ∏ j ∈ A, x j := by
  have hdiff : D * (∏ j ∈ B \ A, x j) < ∏ j ∈ A \ B, x j :=
    product_dominance_of_lower_indices x D hx hD (A \ B) (B \ A) i
      (Finset.mem_sdiff.mpr ⟨hiA, hiB⟩) hB hgrowth
  have hcommon : 0 < ∏ j ∈ A ∩ B, x j :=
    Finset.prod_pos (fun j _ => lt_of_lt_of_le zero_lt_one (hx j))
  calc
    D * (∏ j ∈ B, x j)
        = (∏ j ∈ A ∩ B, x j) * (D * (∏ j ∈ B \ A, x j)) := by
            rw [← Finset.prod_inter_mul_prod_sdiff B A x, Finset.inter_comm B A]
            ac_rfl
    _ < (∏ j ∈ A ∩ B, x j) * (∏ j ∈ A \ B, x j) :=
      mul_lt_mul_of_pos_left hdiff hcommon
    _ = ∏ j ∈ A, x j := Finset.prod_inter_mul_prod_sdiff A B x

end PiExponent

end OAI
