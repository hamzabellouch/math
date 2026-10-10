import OAI.GroupTheory.PolycyclicRecognition.Geometry.WeightedColumnBasis

namespace OAI

/-! # The converse basis-exchange criterion

An invertible selected basis is maximizing if every nonzero coordinate of
each available vector lies in a basis direction of at least its weight.
The determinant permutation supplies the required matching for any rival
basis. This is used to extend an ideal basis by zero-width pure words.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators

theorem maximizingColumnBasis_of_coordinate_support {I : Type*} {n : ℕ}
    (v : I → Fin n → ℝ) (w : I → ℝ) (b : Fin n → I)
    (hb : (columnBasisMatrix v b).det ≠ 0)
    (hcoord : ∀ y j, columnCoordinates v b y j ≠ 0 → w y ≤ w (b j)) :
    IsMaximizingColumnBasis v w b := by
  classical
  refine ⟨hb, ?_⟩
  intro d hd
  let A := (columnBasisMatrix v b)⁻¹ * columnBasisMatrix v d
  have hA : A.det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
    exact mul_ne_zero (inv_ne_zero hb) hd
  have hsum : (∑ σ : Equiv.Perm (Fin n),
      Equiv.Perm.sign σ • ∏ i, A (σ i) i) ≠ 0 := by
    rw [← Matrix.det_apply]
    exact hA
  obtain ⟨σ, _, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  have hentries (i : Fin n) : A (σ i) i ≠ 0 := by
    intro hz
    have hp : (∏ j, A (σ j) j) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hz
    exact hσ (by rw [hp, smul_zero])
  have hc (i : Fin n) : w (d i) ≤ w (b (σ i)) := by
    apply hcoord
    have he : columnCoordinates v b (d i) (σ i) = A (σ i) i := by
      simp only [columnCoordinates, A, Matrix.mul_apply, Matrix.mulVec, dotProduct,
        columnBasisMatrix]
    rw [he]
    exact hentries i
  change (∑ i, w (d i)) ≤ ∑ i, w (b i)
  exact (Finset.sum_le_sum (fun i _ => hc i)).trans_eq (Equiv.sum_comp σ (fun i => w (b i)))

end PolycyclicRecognition

end

end OAI
