import OAI.Geometry.NodalSets.Elliptic.RealMatrixEnergy

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section

lemma real_young_quarter (k a b : ℝ) (hk : 0 < k) :
    a*b ≤ k/4*a^2+k⁻¹*b^2 := by
  have hi : k*k⁻¹=1 := mul_inv_cancel₀ hk.ne'
  have h := sq_nonneg (k*a-2*b)
  have ht := mul_nonneg (inv_nonneg.mpr hk.le) h
  nlinarith [hi]

lemma real_dot_young_quarter (k : ℝ) (hk : 0 < k) (v w : Yau.Jets.Coord) :
    (∑ i, v i*w i) ≤ k/4*(∑ i, v i^2)+k⁻¹*(∑ i, w i^2) := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ real_young_quarter k (v i) (w i) hk)
  simpa only [Finset.sum_add_distrib,← Finset.mul_sum] using h

lemma real_dot_young (v w : Yau.Jets.Coord) :
    2*(∑ i, v i*w i) ≤ (∑ i, v i^2)+(∑ i, w i^2) := by
  have h := Finset.sum_nonneg (s := Finset.univ) (fun i _ ↦ sq_nonneg (v i-w i))
  simp only [sub_sq,Finset.sum_add_distrib,Finset.sum_sub_distrib,mul_assoc,← Finset.mul_sum] at h
  nlinarith only [h]

lemma real_matrix_cutoff_absorption (B : Matrix (Fin 4) (Fin 4) ℝ)
    (hs : ∀ i j, B i j = B j i)
    (hn : ∀ v : Yau.Jets.Coord, 0 ≤ coordMatrixForm B v v)
    (eta W : ℝ) (g d : Yau.Jets.Coord) :
    -(2*eta*W*coordMatrixForm B d g) ≤
      (eta^2*coordMatrixForm B g g)/4+4*W^2*coordMatrixForm B d d := by
  have h := hn (eta • g+(4*W) • d)
  simp only [map_add,map_smul,_root_.add_apply,_root_.smul_apply,smul_eq_mul] at h
  rw [coordMatrixForm_symmetric B hs g d] at h
  nlinarith only [h]

end
end Yau.Geometry

end OAI
