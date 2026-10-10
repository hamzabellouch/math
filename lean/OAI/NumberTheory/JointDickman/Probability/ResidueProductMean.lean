import OAI.NumberTheory.JointDickman.Arithmetic.DivisorProductMean
import OAI.NumberTheory.JointDickman.Probability.ResidueQuotientMean

namespace OAI

/-! # Exact means of finite prime-divisor products -/

namespace JointDickman
open Finset

open Classical in
theorem residue_divisor_mean {d q : ℕ} [NeZero d] [NeZero q] (hd : d ∣ q) :
    (∑ a : ZMod q, if d ∣ a.val then (1 : ℝ) else 0) / (q : ℝ) = 1 / (d : ℝ) := by
  have h := residue_quotient_mean hd (fun a : ZMod d => if a = 0 then (1 : ℝ) else 0)
  simpa only [ZMod.natCast_eq_zero_iff, sum_ite_eq', mem_univ, ite_true] using h

open Classical in
/-- Uniform residues give the exact finite Euler-product mean. -/
theorem residue_divisor_product_mean (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {q : ℕ} [NeZero q] (hdiv : (∏ p ∈ P, p) ∣ q) (b : ℕ → ℝ) :
    (∑ a : ZMod q, ∏ p ∈ P, if p ∣ a.val then 1+b p else 1) / (q : ℝ) =
      ∏ p ∈ P, (1+b p/(p : ℝ)) := by
  simp_rw [divisor_product_expansion P hP b]
  rw [sum_comm, sum_div]
  rw [prod_one_add]
  apply sum_congr rfl
  intro D hD
  have hDP := mem_powerset.mp hD
  have hd : (∏ p ∈ D, p) ∣ q := (prod_dvd_prod_of_subset _ _ id hDP).trans hdiv
  let : NeZero (∏ p ∈ D, p) := ⟨prod_ne_zero_iff.mpr (fun p hp => (hP p (hDP hp)).ne_zero)⟩
  have he : (∑ a : ZMod q, if (∏ p ∈ D, p) ∣ a.val then ∏ p ∈ D, b p else 0) =
      (∏ p ∈ D, b p) * ∑ a : ZMod q, if (∏ p ∈ D, p) ∣ a.val then (1 : ℝ) else 0 := by
    rw [mul_sum]
    apply sum_congr rfl
    intro a _
    split_ifs <;> simp
  rw [he, mul_div_assoc, residue_divisor_mean hd, prod_div_distrib, Nat.cast_prod]
  ring

end JointDickman

end OAI
