import Mathlib
import OAI.Analysis.AffineBernstein.AffineFamily

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

open Matrix
open scoped MatrixOrder

lemma tracefree_sum_square_bound {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℝ)
    (ha : ∑ i, a i = 0) (i : Fin n) :
    ((n:ℝ)+1)*(a i)^2 ≤ (n:ℝ)*(∑ j, (a j)^2) := by
  have he := Finset.sum_erase_add (s := Finset.univ) a (Finset.mem_univ i)
  have he2 := Finset.sum_erase_add (s := Finset.univ) (fun j => (a j)^2) (Finset.mem_univ i)
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ.erase i) (f := a)
  have hcard : ((Finset.univ.erase i).card : ℝ) = (n:ℝ)-1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i),Finset.card_univ,Fintype.card_fin,Nat.cast_sub hn]
    norm_num
  rw [hcard] at hcs
  rw [ha] at he
  have hsum : 0 ≤ ∑ j, (a j)^2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hse : (∑ x ∈ Finset.univ.erase i, a x) = -a i := by linarith
  have hse2 : (∑ x ∈ Finset.univ.erase i, a x^2) = (∑ j, (a j)^2)-(a i)^2 := by linarith
  rw [hse,hse2,neg_sq] at hcs
  have hbase : (n:ℝ)*(a i)^2 ≤ ((n:ℝ)-1)*(∑ j, (a j)^2) := by nlinarith
  have ht := mul_le_mul_of_nonneg_left hbase (show 0 ≤ (n:ℝ)+1 by positivity)
  apply (mul_le_mul_iff_left₀ (show (0:ℝ)<n by linarith)).mp
  nlinarith [ht]

lemma tracefree_matrix_gap {n : ℕ} (hn : 1 ≤ n)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsHermitian) (htr : B.trace=0) :
    (((n:ℝ)*(B*B).trace) • (1 : Matrix (Fin n) (Fin n) ℝ) - ((n:ℝ)+1) • (B*B)).PosSemidef := by
  let a := hB.eigenvalues
  have ha : ∑ i, a i=0 := by simpa [a,hB.trace_eq_sum_eigenvalues] using htr
  let U := hB.eigenvectorUnitary
  let D : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal a
  have hBD : B = (U:Matrix (Fin n) (Fin n) ℝ) * D * (U:Matrix (Fin n) (Fin n) ℝ).conjTranspose := by
    simpa [a,U,D,Unitary.conjStarAlgAut_apply,Matrix.star_eq_conjTranspose] using hB.spectral_theorem
  have hUU : (U:Matrix (Fin n) (Fin n) ℝ).conjTranspose * (U:Matrix (Fin n) (Fin n) ℝ) = 1 :=
    Unitary.coe_star_mul_self U
  have hUU' : (U:Matrix (Fin n) (Fin n) ℝ) * (U:Matrix (Fin n) (Fin n) ℝ).conjTranspose = 1 :=
    Unitary.coe_mul_star_self U
  have hB2 : B*B = (U:Matrix (Fin n) (Fin n) ℝ) * (D*D) * (U:Matrix (Fin n) (Fin n) ℝ).conjTranspose := by
    rw [hBD]
    simp only [Matrix.mul_assoc,← Matrix.mul_assoc (U:Matrix (Fin n) (Fin n) ℝ).conjTranspose, hUU,Matrix.one_mul]
  have ht : (B*B).trace = ∑ i, (a i)^2 := by
    rw [hB2,Matrix.trace_mul_cycle,hUU,Matrix.one_mul]
    simp [D,Matrix.diagonal_mul_diagonal,pow_two,Matrix.trace_diagonal]
  have hp : (((n:ℝ)*(∑ i, (a i)^2)) • (1 : Matrix (Fin n) (Fin n) ℝ) - ((n:ℝ)+1) • (D*D)).PosSemidef := by
    have hd : ((n:ℝ)*(∑ i, (a i)^2)) • (1 : Matrix (Fin n) (Fin n) ℝ) - ((n:ℝ)+1) • (D*D) =
        Matrix.diagonal (fun i => (n:ℝ)*(∑ j, (a j)^2)-((n:ℝ)+1)*(a i)^2) := by
      ext i j
      by_cases hij : i=j
      · subst j
        simp [D,Matrix.diagonal_mul_diagonal,pow_two]
      · simp [D,Matrix.diagonal_mul_diagonal,hij]
    rw [hd,Matrix.posSemidef_diagonal_iff]
    intro i
    exact sub_nonneg.mpr (tracefree_sum_square_bound hn a ha i)
  have hh := hp.mul_mul_conjTranspose_same (U:Matrix (Fin n) (Fin n) ℝ)
  simpa only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,hUU',← hB2,← ht] using hh

end AffineBernstein

end

end OAI
