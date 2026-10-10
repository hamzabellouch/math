import OAI.Analysis.FreeEntropy.SpectralClustering

namespace OAI

noncomputable section
open Finset
open scoped ComplexConjugate
namespace FiniteEntropySeparation
variable {p d : ℕ}
 theorem small_rows_bound (W : Fin d → Fin d → ℝ) (hW : ∀j k,0≤W j k)
    (B : Finset (Fin d)) (hb : (B.card:ℝ)≤(d:ℝ)/4096)
    (hfour : (∑j : Fin d,(∑k : Fin d,W j k)^2)≤4*d) :
    (∑j∈B,∑k : Fin d,W j k)≤(d:ℝ)/32 := by
  have hrows : ∀ j, 0 ≤ ∑ k : Fin d, W j k := fun j => sum_nonneg (fun k _ => hW j k)
  have hc := sq_sum_le_card_mul_sum_sq (s := B) (f := fun j => ∑k : Fin d,W j k)
  have hh : (∑j∈B,(∑k : Fin d,W j k)^2)≤4*d :=
    (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => sq_nonneg _)).trans hfour
  have hm := mul_le_mul hb hh (sum_nonneg (fun j _ => pow_nonneg (hrows j) 2)) (by positivity : (0:ℝ)≤d/4096)
  have hd : (0:ℝ)≤d := by positivity
  nlinarith
 theorem clustered_energy_lower [NeZero p] (y : Fin p → ℝ) (δ Δ : ℝ) (x : Fin d → ℝ)
    (hy : ∀i j,i≠j → Δ≤|y i-y j|) (hδ : δ≤Δ/4) (hΔ : 0<Δ)
    (W : Fin d → Fin d → ℝ) (hW : ∀j k,0≤W j k) (hsymm : ∀j k,W j k=W k j)
    (hsecond : 3*(d:ℝ)/4≤∑j,∑k,W j k)
    (hfour : (∑j : Fin d,(∑k : Fin d,W j k)^2)≤4*d)
    (hcomm : (∑j,∑k,(x j-x k)^2*W j k)≤Δ^2*d/64)
    (hb : ((badSpectrum y δ x).card:ℝ)≤(d:ℝ)/4096) :
    (d:ℝ)/2≤∑j,∑k,if clusterLabel y δ x j=clusterLabel y δ x k then W j k else 0 := by
  classical
  let B := badSpectrum y δ x
  have hrows := small_rows_bound W hW B hb hfour
  have hpoint j k : W j k ≤
      (if clusterLabel y δ x j=clusterLabel y δ x k then W j k else 0)+
      (4/Δ^2)*((x j-x k)^2*W j k)+
      (if j∈B then W j k else 0)+(if k∈B then W j k else 0) := by
    have hn := hW j k
    have hc : 0≤(4/Δ^2)*((x j-x k)^2*W j k) := by positivity
    by_cases he : clusterLabel y δ x j=clusterLabel y δ x k
    · simp only [ite_eq_left he]; split_ifs <;> linarith
    by_cases hj : j∈B
    · simp only [ite_eq_right he,ite_eq_left hj]; split_ifs <;> linarith
    by_cases hk : k∈B
    · simp only [ite_eq_right he,ite_eq_left hk]; split_ifs ; linarith
    simp only [ite_eq_right he,ite_eq_right hj,ite_eq_right hk,zero_add,add_zero]
    have hs := clusterLabel_separated y δ Δ x hy hδ hj hk he
    have hs' : Δ^2/4≤(x j-x k)^2 := by nlinarith [sq_abs (x j-x k)]
    have hf : 1≤(4/Δ^2)*(x j-x k)^2 := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ (sq_pos_of_pos hΔ)).mpr
      nlinarith
    have hm := mul_le_mul_of_nonneg_right hf hn
    nlinarith
  have hh := sum_le_sum (fun j (_ : j∈(univ:Finset (Fin d))) => sum_le_sum (fun k (_ : k∈(univ:Finset (Fin d))) => hpoint j k))
  have he1 : (∑j : Fin d,∑k : Fin d,if j∈B then W j k else 0)=∑j∈B,∑k : Fin d,W j k := by
    calc
      _ = ∑j : Fin d,if j∈B then ∑k : Fin d,W j k else 0 := by
        apply sum_congr rfl
        intro j _
        by_cases hj : j∈B <;> simp [hj]
      _ = _ := by simp
  have he2 : (∑j : Fin d,∑k : Fin d,if k∈B then W j k else 0)=∑j∈B,∑k : Fin d,W j k := by
    rw [sum_comm]
    simpa only [hsymm] using he1
  simp only [sum_add_distrib,← mul_sum,he1,he2] at hh
  have hc := mul_le_mul_of_nonneg_left hcomm (show 0≤4/Δ^2 by positivity)
  have hc' : (4/Δ^2)*(∑j,∑k,(x j-x k)^2*W j k)≤(d:ℝ)/16 := by
    calc
      _ ≤ (4/Δ^2)*(Δ^2*(d:ℝ)/64) := hc
      _ = _ := by field_simp [ne_of_gt hΔ]; ring
  linarith
 theorem hermitian_row_energy (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (j : Fin d) :
    ∑k,Complex.normSq (A j k)=((A^2) j j).re := by
  have he k : star (A j k)=A k j := by simpa only [Matrix.conjTranspose_apply] using congrFun (congrFun hA.eq k) j
  rw [pow_two,Matrix.mul_apply,Complex.re_sum]
  apply sum_congr rfl
  intro k _
  rw [← he k,Complex.star_def,Complex.mul_conj,Complex.ofReal_re]
 theorem hermitian_row_fourth (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) :
    (∑j : Fin d,(∑k : Fin d,Complex.normSq (A j k))^2)≤(Matrix.trace (A^4)).re := by
  have hA2 : (A^2).IsHermitian := hA.pow 2
  have ht : (Matrix.trace (A^4)).re=hsNorm (A^2)^2 := by
    rw [hsNorm_sq,← trace_conjTranspose_mul_re,hA2.eq,← pow_add]
  rw [ht,hsNorm_sq]
  apply sum_le_sum
  intro j _
  rw [hermitian_row_energy A hA]
  apply le_trans _ (Finset.single_le_sum (fun k _ => Complex.normSq_nonneg ((A^2) j k)) (mem_univ j))
  simp only [Complex.normSq_apply]
  nlinarith [sq_nonneg ((A^2) j j).im]
 theorem hermitian_entry_symmetric (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (j k : Fin d) :
    Complex.normSq (A j k)=Complex.normSq (A k j) := by
  have he : star (A j k)=A k j := by simpa only [Matrix.conjTranspose_apply] using congrFun (congrFun hA.eq k) j
  rw [← he,Complex.star_def,Complex.normSq_conj]
 theorem commutator_diagonal_entry (A : Matrix (Fin d) (Fin d) ℂ) (x : Fin d → ℝ) (j k : Fin d) :
    Complex.normSq ((Matrix.diagonal (fun j => (x j:ℂ))*A-A*Matrix.diagonal (fun j => (x j:ℂ))) j k)=
      (x j-x k)^2*Complex.normSq (A j k) := by
  simp only [Matrix.sub_apply,Matrix.diagonal_mul,Matrix.mul_diagonal]
  rw [mul_comm (A j k),← sub_mul,← Complex.ofReal_sub,Complex.normSq_mul,Complex.normSq_ofReal]
  ring
end FiniteEntropySeparation

end

end OAI
