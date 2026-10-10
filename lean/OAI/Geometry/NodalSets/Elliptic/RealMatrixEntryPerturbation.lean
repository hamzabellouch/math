import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import OAI.Geometry.NodalSets.Elliptic.RealMatrixEnergy

namespace OAI

namespace Yau.Geometry
noncomputable section

theorem real_matrix_entry_perturbation (A B : Matrix (Fin 4) (Fin 4) ℝ)
    (eps : ℝ) (heps : 0 ≤ eps) (hAB : ∀ i j, |A i j-B i j| ≤ eps)
    (z : Yau.Jets.Coord) :
    |(∑ i, ∑ j, z i*A i j*z j)-(∑ i, ∑ j, z i*B i j*z j)| ≤
      16*eps*(∑ i, z i^2) := by
  let S : ℝ := ∑ i, z i^2
  have hzi (i : Fin 4) : (z i)^2 ≤ S :=
    Finset.single_le_sum (fun j _ ↦ sq_nonneg (z j)) (Finset.mem_univ i)
  have hz (i j : Fin 4) : |z i| * |z j| ≤ S := by
    nlinarith [sq_abs (z i),sq_abs (z j),sq_nonneg (|z i|-|z j|),hzi i,hzi j]
  have ht (i j : Fin 4) : |z i*(A i j-B i j)*z j| ≤ eps*S := by
    rw [abs_mul,abs_mul]
    have h := mul_le_mul_of_nonneg_left (hAB i j) (mul_nonneg (abs_nonneg (z i)) (abs_nonneg (z j)))
    have h' := mul_le_mul_of_nonneg_left (hz i j) heps
    nlinarith only [h,h']
  have he : (∑ i, ∑ j, z i*A i j*z j)-(∑ i, ∑ j, z i*B i j*z j)=
      ∑ i, ∑ j, z i*(A i j-B i j)*z j := by
    simp only [mul_sub,sub_mul,Finset.sum_sub_distrib]
  rw [he]
  calc
    _ ≤ ∑ i, |∑ j, z i*(A i j-B i j)*z j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |z i*(A i j-B i j)*z j| :=
      Finset.sum_le_sum (fun i _ ↦ Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : Fin 4, ∑ _j : Fin 4, eps*S :=
      Finset.sum_le_sum (fun i _ ↦ Finset.sum_le_sum (fun j _ ↦ ht i j))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

end
end Yau.Geometry

end OAI
