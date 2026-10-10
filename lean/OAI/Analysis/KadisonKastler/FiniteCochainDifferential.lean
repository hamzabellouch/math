import OAI.Analysis.KadisonKastler.FiniteHaagerupBounds

namespace OAI

/-! Hochschild matrix identities with arbitrary finite intermediate indices. -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

@[simp] theorem finiteBilinearProduct_apply (f : A →ₗ[ℂ] A →ₗ[ℂ] A)
    {p r q : Type*} [Fintype r] (X : CStarMatrix p r A) (Y : CStarMatrix r q A)
    (i : p) (j : q) : finiteBilinearProduct f X Y i j = ∑ k, f (X i k) (Y k j) := rfl

@[simp] theorem finiteBilinearProduct_mul {p r q : Type*} [Fintype r]
    (X : CStarMatrix p r A) (Y : CStarMatrix r q A) :
    finiteBilinearProduct (LinearMap.mul ℂ A) X Y = X * Y := by ext; rfl

@[simp] theorem finiteBilinearProduct_add (f g : A →ₗ[ℂ] A →ₗ[ℂ] A) {p r q : Type*} [Fintype r]
    (X : CStarMatrix p r A) (Y : CStarMatrix r q A) :
    finiteBilinearProduct (f + g) X Y = finiteBilinearProduct f X Y + finiteBilinearProduct g X Y := by
  ext i j
  simp only [finiteBilinearProduct_apply, LinearMap.add_apply, Finset.sum_add_distrib, CStarMatrix.add_apply]

@[simp] theorem finiteBilinearProduct_sub (f g : A →ₗ[ℂ] A →ₗ[ℂ] A) {p r q : Type*} [Fintype r]
    (X : CStarMatrix p r A) (Y : CStarMatrix r q A) :
    finiteBilinearProduct (f - g) X Y = finiteBilinearProduct f X Y - finiteBilinearProduct g X Y := by
  ext i j
  simp only [finiteBilinearProduct_apply, LinearMap.sub_apply, Finset.sum_sub_distrib, CStarMatrix.sub_apply]

@[simp] theorem finiteBilinearProduct_add_left (f : A →ₗ[ℂ] A →ₗ[ℂ] A) {p r q : Type*} [Fintype r]
    (X X' : CStarMatrix p r A) (Y : CStarMatrix r q A) :
    finiteBilinearProduct f (X + X') Y = finiteBilinearProduct f X Y + finiteBilinearProduct f X' Y := by
  ext i j
  simp [map_add, Finset.sum_add_distrib]

@[simp] theorem finiteBilinearProduct_add_right (f : A →ₗ[ℂ] A →ₗ[ℂ] A) {p r q : Type*} [Fintype r]
    (X : CStarMatrix p r A) (Y Y' : CStarMatrix r q A) :
    finiteBilinearProduct f X (Y + Y') = finiteBilinearProduct f X Y + finiteBilinearProduct f X Y' := by
  ext i j
  simp [map_add, Finset.sum_add_distrib]

@[simp] theorem finiteBilinearProduct_smul (z : ℂ) (f : A →ₗ[ℂ] A →ₗ[ℂ] A) {p r q : Type*} [Fintype r]
    (X : CStarMatrix p r A) (Y : CStarMatrix r q A) :
    finiteBilinearProduct (z • f) X Y = z • finiteBilinearProduct f X Y := by
  ext i j
  change (∑ k, z • f (X i k) (Y k j)) = z • ∑ k, f (X i k) (Y k j)
  rw [Finset.smul_sum]

/-- Algebraic associativity survives every rectangular matrix amplification. -/
theorem finiteBilinearProduct_assoc (m : A →ₗ[ℂ] A →ₗ[ℂ] A)
    (hm : ∀ x y z, m (m x y) z = m x (m y z)) {p r s q : Type*} [Fintype r] [Fintype s]
    (X : CStarMatrix p r A) (Y : CStarMatrix r s A)
    (Z : CStarMatrix s q A) :
    finiteBilinearProduct m (finiteBilinearProduct m X Y) Z =
      finiteBilinearProduct m X (finiteBilinearProduct m Y Z) := by
  ext i l
  simp only [finiteBilinearProduct_apply, map_sum, LinearMap.sum_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => hm _ _ _

theorem rectangular_mul_assoc_finite {p r s q : Type*} [Fintype r] [Fintype s]
    (X : CStarMatrix p r A) (Y : CStarMatrix r s A)
    (Z : CStarMatrix s q A) : (X * Y) * Z = X * (Y * Z) := by
  ext i l
  change (∑ k, (∑ j, X i j * Y j k) * Z k l) =
    ∑ j, X i j * (∑ k, Y j k * Z k l)
  simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

/-- The degree-two Hochschild differential, already amplified to matrices. -/
def finiteMatrixDifferential (f : A →ₗ[ℂ] A →ₗ[ℂ] A) {p r s q : Type*} [Fintype r] [Fintype s]
    (X : CStarMatrix p r A) (Y : CStarMatrix r s A)
    (Z : CStarMatrix s q A) : CStarMatrix p q A :=
  X * finiteBilinearProduct f Y Z - finiteBilinearProduct f (X * Y) Z +
    finiteBilinearProduct f X (Y * Z) - finiteBilinearProduct f X Y * Z

/-- The Maurer--Cartan identity, with its signs fixed for the correction step. -/
theorem finiteMatrixDifferential_defect (m : A →ₗ[ℂ] A →ₗ[ℂ] A)
    (hm : ∀ x y z, m (m x y) z = m x (m y z)) {p r s q : Type*} [Fintype r] [Fintype s]
    (X : CStarMatrix p r A) (Y : CStarMatrix r s A)
    (Z : CStarMatrix s q A) :
    let f := m - LinearMap.mul ℂ A
    finiteMatrixDifferential f X Y Z =
      finiteBilinearProduct f (finiteBilinearProduct f X Y) Z -
        finiteBilinearProduct f X (finiteBilinearProduct f Y Z) := by
  let f := m - LinearMap.mul ℂ A
  have hm' : m = LinearMap.mul ℂ A + f := by dsimp [f]; abel
  have he := finiteBilinearProduct_assoc m hm X Y Z
  rw [hm'] at he
  simp only [finiteBilinearProduct_add, finiteBilinearProduct_mul, finiteBilinearProduct_add_left,
    finiteBilinearProduct_add_right, rectangular_mul_assoc_finite] at he
  dsimp only [finiteMatrixDifferential]
  change X * finiteBilinearProduct f Y Z - finiteBilinearProduct f (X * Y) Z +
      finiteBilinearProduct f X (Y * Z) - finiteBilinearProduct f X Y * Z = _
  have he' := congrArg (fun T => T - (X * Y) * Z -
    finiteBilinearProduct f (X * Y) Z - finiteBilinearProduct f X Y * Z -
    finiteBilinearProduct f X (finiteBilinearProduct f Y Z)) he
  rw [← rectangular_mul_assoc_finite] at he'
  symm
  convert he' using 1 <;> abel

variable [PartialOrder A] [StarOrderedRing A]

theorem finiteMatrixDifferential_defect_bound
    (m : A →ₗ[ℂ] A →ₗ[ℂ] A)
    (hm : ∀ x y z, m (m x y) z = m x (m y z)) {c : ℝ} (hc : 0 ≤ c)
    (hf : HaagerupBound (m - LinearMap.mul ℂ A) c) {p r s q : Type*} [Fintype p] [Fintype r] [Fintype s] [Fintype q]
    (X : CStarMatrix p r A) (Y : CStarMatrix r s A)
    (Z : CStarMatrix s q A) :
    ‖finiteMatrixDifferential (m - LinearMap.mul ℂ A) X Y Z‖ ≤
      2 * c ^ 2 * ‖X‖ * ‖Y‖ * ‖Z‖ := by
  rw [finiteMatrixDifferential_defect m hm]
  calc
    _ ≤ ‖finiteBilinearProduct (m - LinearMap.mul ℂ A)
          (finiteBilinearProduct (m - LinearMap.mul ℂ A) X Y) Z‖ +
        ‖finiteBilinearProduct (m - LinearMap.mul ℂ A) X
          (finiteBilinearProduct (m - LinearMap.mul ℂ A) Y Z)‖ := norm_sub_le _ _
    _ ≤ c * (c * ‖X‖ * ‖Y‖) * ‖Z‖ + c * ‖X‖ * (c * ‖Y‖ * ‖Z‖) := by
      apply add_le_add
      · exact (hf.finite _ Z).trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hf.finite X Y) hc) (norm_nonneg Z))
      · exact (hf.finite X _).trans (mul_le_mul_of_nonneg_left
          (hf.finite Y Z) (mul_nonneg hc (norm_nonneg X)))
    _ = _ := by ring

end

end KadisonKastler

end OAI
