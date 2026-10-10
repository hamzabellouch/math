import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic

namespace OAI

/-! # Relative errors in the finite product of internal-prime averages -/

namespace Ostmann
open scoped BigOperators

/-- A common local majorant retains the full product scale in the error. -/
theorem finite_relative_product_error {ι : Type*} (S : Finset ι)
    (f g : ι → ℂ) (B K : ι → ℝ)
    (hB : ∀ i ∈ S, 0 ≤ B i) (hK : ∀ i ∈ S, 0 ≤ K i)
    (hf : ∀ i ∈ S, ‖f i‖ ≤ B i) (hg : ∀ i ∈ S, ‖g i‖ ≤ B i)
    (hdiff : ∀ i ∈ S, ‖f i - g i‖ ≤ K i * B i) :
    ‖(∏ i ∈ S, f i) - ∏ i ∈ S, g i‖ ≤
      (∑ i ∈ S, K i) * ∏ i ∈ S, B i := by
  classical
  revert hB hK hf hg hdiff
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    intro hB hK hf hg hdiff
    have hs (j : ι) (hj : j ∈ S) : j ∈ insert i S := Finset.mem_insert_of_mem hj
    have herr := ih (fun j hj => hB j (hs j hj)) (fun j hj => hK j (hs j hj))
      (fun j hj => hf j (hs j hj)) (fun j hj => hg j (hs j hj))
      (fun j hj => hdiff j (hs j hj))
    have hprod : ‖∏ j ∈ S, g j‖ ≤ ∏ j ∈ S, B j := by
      rw [norm_prod]
      exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j hj => hg j (hs j hj))
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi,
      Finset.prod_insert hi]
    rw [show f i * (∏ j ∈ S, f j) - g i * (∏ j ∈ S, g j) =
      f i * ((∏ j ∈ S, f j) - ∏ j ∈ S, g j) +
        (f i - g i) * ∏ j ∈ S, g j by ring]
    calc
      _ ≤ ‖f i * ((∏ j ∈ S, f j) - ∏ j ∈ S, g j)‖ +
          ‖(f i - g i) * ∏ j ∈ S, g j‖ := norm_add_le _ _
      _ ≤ B i * ((∑ j ∈ S, K j) * ∏ j ∈ S, B j) +
          (K i * B i) * ∏ j ∈ S, B j := by
        rw [norm_mul, norm_mul]
        apply add_le_add
        · exact mul_le_mul (hf i (Finset.mem_insert_self _ _)) herr
            (norm_nonneg _) (hB i (Finset.mem_insert_self _ _))
        · exact mul_le_mul (hdiff i (Finset.mem_insert_self _ _)) hprod
            (norm_nonneg _) (mul_nonneg (hK i (Finset.mem_insert_self _ _))
              (hB i (Finset.mem_insert_self _ _)))
      _ = _ := by ring

end Ostmann

end OAI
