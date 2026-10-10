import OAI.GroupTheory.PolycyclicRecognition.Geometry.PolynomialDifferential
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace OAI

/-! # Polynomial derivative minors and their uniform degree bounds -/

noncomputable section

namespace PolycyclicRecognition

open MvPolynomial Matrix
open scoped BigOperators

theorem totalDegree_pderiv_le {m : ℕ} (p : MvPolynomial (Fin m) ℝ) (j : Fin m) :
    (pderiv j p).totalDegree ≤ p.totalDegree - 1 := by
  classical
  unfold totalDegree
  apply Finset.sup_le
  intro s hs
  have hc : (pderiv j p).coeff s ≠ 0 := mem_support_iff.mp hs
  rw [coeff_pderiv] at hc
  have hp : s + Finsupp.single j 1 ∈ p.support :=
    mem_support_iff.mpr (left_ne_zero_of_mul hc)
  have hd := le_totalDegree hp
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
    Finsupp.sum_single_index (by rfl)] at hd
  change (s.sum fun _ e => e) ≤ p.totalDegree - 1
  omega

def polynomialJacobianMinor {n k : ℕ} (p : Fin n → MvPolynomial (Fin (n + k)) ℝ) :
    MvPolynomial (Fin (n + k)) ℝ :=
  Matrix.det (Matrix.of fun i j => pderiv (Fin.castAdd k j) (p i))

theorem totalDegree_polynomialJacobianMinor_le {n k D : ℕ}
    (p : Fin n → MvPolynomial (Fin (n + k)) ℝ)
    (hp : ∀ i, (p i).totalDegree ≤ D) :
    (polynomialJacobianMinor p).totalDegree ≤ n * (D - 1) := by
  classical
  unfold polynomialJacobianMinor
  rw [Matrix.det_apply]
  apply totalDegree_finsetSum_le
  intro σ _
  calc
    _ ≤ (∏ i, pderiv (Fin.castAdd k i) (p (σ i))).totalDegree :=
      totalDegree_smul_le _ _
    _ ≤ ∑ i : Fin n, (pderiv (Fin.castAdd k i) (p (σ i))).totalDegree :=
      totalDegree_finsetProd _ _
    _ ≤ n * (D - 1) := by
      calc
        _ ≤ ∑ _i : Fin n, (D - 1) := Finset.sum_le_sum (fun i _ =>
          (totalDegree_pderiv_le _ _).trans (Nat.sub_le_sub_right (hp (σ i)) 1))
        _ = _ := by simp

end PolycyclicRecognition

end

end OAI
