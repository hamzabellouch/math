import Mathlib
import OAI.Probability.SKGap.Gaussian.GOERowTail

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real Set
open scoped BigOperators
variable {n : ℕ}

lemma coupling_goe_all_rows_tail [NeZero n] {j t : ℝ} (hj : 0 < j) :
    (gaussianCoordinates (MatrixCoordinates (Fin n))).real
      {g | ∃ i : Fin n,t < ∑ k,coupling (goeDisorder (j/(n:ℝ)) g) i k^2} ≤
      (n:ℝ)*exp (-(n:ℝ)*(t/(4*j)-log 2)) := by
  have hn : (0:ℝ) < n := by exact_mod_cast NeZero.pos n
  have he : {g : MatrixCoordinates (Fin n)→ℝ | ∃ i : Fin n,t < ∑ k,coupling (goeDisorder (j/(n:ℝ)) g) i k^2}=
      ⋃ i : Fin n,{g | t < ∑ k,coupling (goeDisorder (j/(n:ℝ)) g) i k^2} := by ext g;simp
  rw [he]
  apply (measureReal_iUnion_fintype_le _).trans
  have hb (i : Fin n) := coupling_goe_row_tail (div_pos hj hn) i Finset.univ t
  simp only [Finset.card_univ,Fintype.card_fin] at hb
  apply (Finset.sum_le_sum (fun i _=>hb i)).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  congr 2
  field_simp
  ring

lemma coupling_goe_max_entry_tail [NeZero n] {j d : ℝ} (hj : 0 < j) (hd : 0 ≤ d) :
    (gaussianCoordinates (MatrixCoordinates (Fin n))).real
      {g | ∃ i k : Fin n,d < |coupling (goeDisorder (j/(n:ℝ)) g) i k|} ≤
      2*(n:ℝ)^2*exp (-(n:ℝ)*d^2/(4*j)) := by
  have hn : (0:ℝ) < n := by exact_mod_cast NeZero.pos n
  have hsingle (i k : Fin n) :
      (gaussianCoordinates (MatrixCoordinates (Fin n))).real
        {g | d < |coupling (goeDisorder (j/(n:ℝ)) g) i k|} ≤
      2*exp (-(n:ℝ)*d^2/(4*j)) := by
    have he : {g : MatrixCoordinates (Fin n)→ℝ | d < |coupling (goeDisorder (j/(n:ℝ)) g) i k|}=
        {g | d^2 < ∑ l∈({k} : Finset (Fin n)),coupling (goeDisorder (j/(n:ℝ)) g) i l^2} := by
      ext g
      simp only [Finset.sum_singleton,Set.mem_ofPred_eq]
      simpa only [sq_abs] using (sq_lt_sq₀ hd (abs_nonneg (coupling (goeDisorder (j/(n:ℝ)) g) i k))).symm
    rw [he]
    apply (coupling_goe_row_tail (div_pos hj hn) i {k} (d^2)).trans_eq
    simp only [Finset.card_singleton,Nat.cast_one,one_mul,exp_add,exp_log (by norm_num : (0:ℝ) < 2)]
    rw [mul_comm]
    congr 2
    field_simp
  have he : {g : MatrixCoordinates (Fin n)→ℝ | ∃ i k : Fin n,d < |coupling (goeDisorder (j/(n:ℝ)) g) i k|}=
      ⋃ i : Fin n,⋃ k : Fin n,{g | d < |coupling (goeDisorder (j/(n:ℝ)) g) i k|} := by ext g;simp
  rw [he]
  apply (measureReal_iUnion_fintype_le _).trans
  apply (Finset.sum_le_sum (fun i _=>(measureReal_iUnion_fintype_le _).trans (Finset.sum_le_sum (fun k _=>hsingle i k)))).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring
end SKGap

end
end

end OAI
