import Mathlib

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators
variable {I C : Type*} [Fintype I] [DecidableEq I] [CommGroup C] [Fintype C] [DecidableEq C]

theorem product_split_coordinate {M : Type*} [CommMonoid M] (j : I) (f : I → M) :
    (∏ i,f i)=f j*∏ i : {i : I // i≠j},f i := by
  have he : (∏ i : {i : I // i≠j},f i)=∏ i ∈ Finset.univ.erase j,f i := by
    exact (Finset.prod_subtype (Finset.univ.erase j) (fun i => by simp) f).symm
  rw [he]
  exact (Finset.mul_prod_erase Finset.univ f (Finset.mem_univ j)).symm

theorem constrained_character_sum_bound (j : I) (e : I → C ≃ C)
    (w : I → C → ℝ) (hw : ∀ i χ,0≤w i χ) (δ : ℝ) (hδ : ∀ χ,w j χ≤δ) :
    (∑ ρ : I → C, if (∏ i,e i (ρ i))=1 then ∏ i,w i (ρ i) else 0) ≤
      δ*∏ i : {i : I // i≠j},∑ χ : C,w i χ := by
  classical
  let E := Equiv.funSplitAt j C
  let rest (t : ({i : I // i≠j} → C)) : C := ∏ i : {i : I // i≠j},e i (t i)
  let sol (t : ({i : I // i≠j} → C)) : C := (e j).symm ((rest t)⁻¹)
  let W (t : ({i : I // i≠j} → C)) : ℝ := ∏ i : {i : I // i≠j},w i (t i)
  have hE0 (z : C) (t : ({i : I // i≠j} → C)) : E.symm (z,t) j=z := by simp [E]
  have hEi (z : C) (t : ({i : I // i≠j} → C)) (i : {i : I // i≠j}) : E.symm (z,t) i=t i := by simp [E,i.property]
  have hp (z : C) (t : ({i : I // i≠j} → C)) :
      (∏ i,e i (E.symm (z,t) i))=(e j z)*rest t := by
    rw [product_split_coordinate j]
    simp only [hE0,hEi,rest]
  have hwprod (z : C) (t : ({i : I // i≠j} → C)) :
      (∏ i,w i (E.symm (z,t) i))=w j z*W t := by
    rw [product_split_coordinate j]
    simp only [hE0,hEi,W]
  have hconstraint (z : C) (t : ({i : I // i≠j} → C)) : (e j z)*rest t=1 ↔ z=sol t := by
    rw [mul_eq_one_iff_eq_inv]
    exact (e j).eq_symm_apply.symm
  have hs :
      (∑ ρ : I → C, if (∏ i,e i (ρ i))=1 then ∏ i,w i (ρ i) else 0) =
      ∑ t : ({i : I // i≠j} → C),w j (sol t)*W t := by
    rw [← E.symm.sum_comp (fun ρ : I → C => if (∏ i,e i (ρ i))=1 then ∏ i,w i (ρ i) else 0),Fintype.sum_prod_type]
    simp_rw [hp,hwprod]
    have hh (z : C) (t : ({i : I // i≠j} → C)) :
        (if (e j z)*rest t=1 then w j z*W t else 0)=
        if z=sol t then w j z*W t else 0 := by simp only [hconstraint]
    simp_rw [hh]
    rw [Finset.sum_comm]
    simp
  rw [hs]
  calc
    _ ≤ ∑ t : ({i : I // i≠j} → C),δ*W t := by
      apply Finset.sum_le_sum
      intro t _
      exact mul_le_mul_of_nonneg_right (hδ _) (Finset.prod_nonneg (fun i _ => hw i (t i)))
    _ = δ*(∑ t : ({i : I // i≠j} → C),∏ i : {i : I // i≠j},w i (t i)) := by rw [Finset.mul_sum]
    _ = _ := by rw [← Fintype.prod_sum]

end
end Ostmann.FiniteField

end OAI
