import Mathlib
import OAI.Probability.SKGap.Entropy.SparseSubsetEntropy
import OAI.Probability.SKGap.Matrix.TanhMatrixBounds
import OAI.Probability.SKGap.Matrix.GOERowLaw

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real Set
open scoped BigOperators
variable {n : ℕ}

lemma coupling_goe_offdiag (r : ℝ) (g : MatrixCoordinates (Fin n)→ℝ) (i k : Fin n)
    (hik : i≠k) : coupling (goeDisorder r g) i k=goeMatrix r g i k := by
  have h := congrFun (congrFun (coupling_goeDisorder r g) i) k
  simpa only [of_apply,Matrix.sub_apply,diagonal_apply_ne _ hik,sub_zero] using h

lemma coupling_goe_row_square_sum (r : ℝ) (g : MatrixCoordinates (Fin n)→ℝ)
    (i : Fin n) (S : Finset (Fin n)) :
    (∑ k∈S,coupling (goeDisorder r g) i k^2)=∑ k : S.erase i,goeMatrix r g i k^2 := by
  rw [Finset.sum_coe_sort (S.erase i) (fun k : Fin n=>goeMatrix r g i k^2)]
  calc
    _ = ∑ k∈S.erase i,coupling (goeDisorder r g) i k^2 :=
      by
        by_cases hi : i∈S
        · rw [Finset.sum_erase_eq_sub hi]
          simp [coupling]
        · rw [Finset.erase_eq_self.mpr hi]
    _ = _ := Finset.sum_congr rfl (fun k hk=>by rw [coupling_goe_offdiag r g i k (Ne.symm (Finset.ne_of_mem_erase hk))])

lemma coupling_goe_row_tail {r : ℝ} (hr : 0 < r) (i : Fin n) (S : Finset (Fin n)) (t : ℝ) :
    (gaussianCoordinates (MatrixCoordinates (Fin n))).real
      {g | t < ∑ k∈S,coupling (goeDisorder r g) i k^2} ≤
      exp (-t/(4*r)+(S.card:ℝ)*log 2) := by
  let e : S.erase i ↪ Fin n := ⟨Subtype.val,Subtype.val_injective⟩
  have havoid (k : S.erase i) : e k≠i := Finset.ne_of_mem_erase k.2
  have hm : MeasurableSet {v : S.erase i→ℝ | t < ∑ k,v k^2} := by measurability
  simp_rw [coupling_goe_row_square_sum]
  have heq := (goe_row_hasLaw hr.le i e havoid).measureReal_eq hm
  change (gaussianCoordinates (MatrixCoordinates (Fin n))).real
    {g | t < ∑ k : S.erase i,goeMatrix r g i k^2} = (Measure.pi (fun _ : S.erase i=>gaussianReal 0 (Real.toNNReal r))).real {v | t < ∑ k,v k^2} at heq
  rw [heq]
  apply (scaled_gaussian_square_tail hr t).trans
  apply exp_le_exp.mpr
  have hcard : (Fintype.card (S.erase i):ℝ) ≤ S.card := by
    rw [Fintype.card_coe]
    exact_mod_cast Finset.card_erase_le
  exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hcard (log_nonneg (show (1:ℝ) ≤ 2 by norm_num)))

lemma coupling_goe_sparse_rows_tail [NeZero n] {j α l t : ℝ}
    (hj : 0 < j) (_hα : 0 ≤ α) (hl : 0 ≤ l) :
    (gaussianCoordinates (MatrixCoordinates (Fin n))).real
      {g | ∃ i : Fin n,∃ S : Finset (Fin n),(S.card:ℝ) ≤ α*(n:ℝ) ∧
        t < ∑ k∈S,coupling (goeDisorder (j/(n:ℝ)) g) i k^2} ≤
      (n:ℝ)*exp (-(n:ℝ)*(t/(4*j)-(l*α+log (1+exp (-l))+α*log 2))) := by
  have hn : (0:ℝ) < n := by exact_mod_cast NeZero.pos n
  have hsingle (i : Fin n) :
      (gaussianCoordinates (MatrixCoordinates (Fin n))).real
        {g | ∃ S : Finset (Fin n),(S.card:ℝ) ≤ α*(n:ℝ) ∧
          t < ∑ k∈S,coupling (goeDisorder (j/(n:ℝ)) g) i k^2} ≤
      exp (-(n:ℝ)*(t/(4*j)-(l*α+log (1+exp (-l))+α*log 2))) := by
    have he : {g : MatrixCoordinates (Fin n)→ℝ | ∃ S : Finset (Fin n),(S.card:ℝ) ≤ α*(n:ℝ) ∧
          t < ∑ k∈S,coupling (goeDisorder (j/(n:ℝ)) g) i k^2}=
      ⋃ S∈smallSupports (ι:=Fin n) α,{g | t < ∑ k∈S,coupling (goeDisorder (j/(n:ℝ)) g) i k^2} := by
      ext g;simp [smallSupports]
    rw [he]
    have hb := sparse_union_bound (gaussianCoordinates (MatrixCoordinates (Fin n)))
      (ι:=Fin n) (C:=1) (q:=t/(4*j)-α*log 2) (α:=α)
      (fun S=>{g | t < ∑ k∈S,coupling (goeDisorder (j/(n:ℝ)) g) i k^2}) hl (by norm_num : (0:ℝ) ≤ 1) ?_
    · convert hb using 1
      simp only [one_mul,Fintype.card_fin]
      congr 1
      ring
    intro S hS
    have hc : (S.card:ℝ) ≤ α*(n:ℝ) := by simpa only [Fintype.card_fin] using (Finset.mem_filter.mp hS).2
    apply (coupling_goe_row_tail (div_pos hj hn) i S t).trans
    simp only [one_mul,Fintype.card_fin]
    apply exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hc (log_nonneg (show (1:ℝ) ≤ 2 by norm_num))
    have he' : -t/(4*(j/(n:ℝ))) = -(n:ℝ)*(t/(4*j)) := by field_simp
    rw [he']
    nlinarith only [hh]
  have he : {g : MatrixCoordinates (Fin n)→ℝ | ∃ i : Fin n,∃ S : Finset (Fin n),(S.card:ℝ) ≤ α*(n:ℝ) ∧
        t < ∑ k∈S,coupling (goeDisorder (j/(n:ℝ)) g) i k^2}=
      ⋃ i : Fin n,{g | ∃ S : Finset (Fin n),(S.card:ℝ) ≤ α*(n:ℝ) ∧
        t < ∑ k∈S,coupling (goeDisorder (j/(n:ℝ)) g) i k^2} := by ext g;simp
  rw [he]
  apply (measureReal_iUnion_fintype_le _).trans
  apply (Finset.sum_le_sum (fun i _=>hsingle i)).trans_eq
  simp
end SKGap

end
end

end OAI
