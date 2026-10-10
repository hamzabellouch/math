import OAI.Geometry.EinsteinFour.ConnectionPullback

namespace OAI

/-! The curvature of the pulled-back connection one-form. The symmetric
second derivative of the coordinate change cancels in the alternating sum. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

theorem matrixPartial_smul (f : FourSpace → ℝ) (A : FourSpace → Mat4)
    (z : FourSpace) (hf : DifferentiableAt ℝ f z)
    (hA : ∀ r s, DifferentiableAt ℝ (fun w => A w r s) z) (i : Fin 4) :
    matrixPartial (fun w => f w • A w) i z =
      partialDeriv f i z • A z + f z • matrixPartial A i z := by
  ext r s
  simp only [matrixPartial, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
    partialDeriv, fderiv_fun_mul hf (hA r s), _root_.add_apply, _root_.smul_apply]
  ring

theorem matrixPartial_sum_four (A : Fin 4 → FourSpace → Mat4) (z : FourSpace)
    (hA : ∀ p r s, DifferentiableAt ℝ (fun w => A p w r s) z) (i : Fin 4) :
    matrixPartial (fun w => ∑ p, A p w) i z = ∑ p, matrixPartial (A p) i z := by
  ext r s
  have hd := fderiv_fun_sum (u := Finset.univ)
    (A := fun p w => A p w r s) (fun p _ => hA p r s)
  change fderiv ℝ (fun w => ∑ p, A p w r s) z (coordinateVector i) =
    ∑ p, fderiv ℝ (fun w => A p w r s) z (coordinateVector i)
  rw [hd, _root_.sum_apply]

def weightedConnectionDerivative (J : Mat4) (P C : Fin 4 → Mat4)
    (D : Fin 4 → Fin 4 → Mat4) (i j : Fin 4) : Mat4 :=
  ∑ a, (P i a j • C a + J a j • ∑ b, J b i • D b a)

theorem weightedConnection_mul (J : Mat4) (C : Fin 4 → Mat4) (i j : Fin 4) :
    weightedConnection J C i * weightedConnection J C j =
      ∑ a, ∑ b, (J a i * J b j) • (C a * C b) := by
  simp only [weightedConnection, Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [mul_comm]

theorem weightedConnection_curvature (J : Mat4) (P C : Fin 4 → Mat4)
    (D : Fin 4 → Fin 4 → Mat4) (hP : ∀ i j a, P i a j = P j a i)
    (i j : Fin 4) :
    weightedConnectionDerivative J P C D i j - weightedConnectionDerivative J P C D j i +
      weightedConnection J C i * weightedConnection J C j -
        weightedConnection J C j * weightedConnection J C i =
      ∑ a, ∑ b, (J a i * J b j) • (D a b - D b a + C a * C b - C b * C a) := by
  have hp : (∑ a, P i a j • C a) = ∑ a, P j a i • C a := by
    apply Finset.sum_congr rfl
    intro a _
    rw [hP i j a]
  have hd : (∑ a, J a j • ∑ b, J b i • D b a) =
      ∑ a, ∑ b, (J a i * J b j) • D a b := by
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [mul_comm]
  have hm : weightedConnection J C j * weightedConnection J C i =
      ∑ a, ∑ b, (J a i * J b j) • (C b * C a) := by
    rw [weightedConnection_mul, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [mul_comm]
  simp only [weightedConnectionDerivative, Finset.sum_add_distrib]
  rw [hp, hd, weightedConnection_mul, hm]
  simp only [Finset.smul_sum, smul_smul, smul_sub, smul_add,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  abel

end
end PositiveEinsteinFour.Geometry

end OAI
