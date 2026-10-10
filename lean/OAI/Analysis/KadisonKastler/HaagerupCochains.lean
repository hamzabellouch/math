import OAI.Analysis.KadisonKastler.Haagerup

namespace OAI

/-! # Matrix Hochschild identities for multiplication correction

The row-column estimates below retain all matrix levels. Associativity turns
the differential of a multiplication defect into a quadratic expression.
-/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

@[simp] theorem bilinearProduct_add (f g : A →ₗ[ℂ] A →ₗ[ℂ] A) {p r q : ℕ}
    (X : CStarMatrix (Fin p) (Fin r) A) (Y : CStarMatrix (Fin r) (Fin q) A) :
    bilinearProduct (f + g) X Y = bilinearProduct f X Y + bilinearProduct g X Y := by
  ext i j
  simp only [bilinearProduct_apply, LinearMap.add_apply, Finset.sum_add_distrib, CStarMatrix.add_apply]

@[simp] theorem bilinearProduct_sub (f g : A →ₗ[ℂ] A →ₗ[ℂ] A) {p r q : ℕ}
    (X : CStarMatrix (Fin p) (Fin r) A) (Y : CStarMatrix (Fin r) (Fin q) A) :
    bilinearProduct (f - g) X Y = bilinearProduct f X Y - bilinearProduct g X Y := by
  ext i j
  simp only [bilinearProduct_apply, LinearMap.sub_apply, Finset.sum_sub_distrib, CStarMatrix.sub_apply]

@[simp] theorem bilinearProduct_add_left (f : A →ₗ[ℂ] A →ₗ[ℂ] A) {p r q : ℕ}
    (X X' : CStarMatrix (Fin p) (Fin r) A) (Y : CStarMatrix (Fin r) (Fin q) A) :
    bilinearProduct f (X + X') Y = bilinearProduct f X Y + bilinearProduct f X' Y := by
  ext i j
  simp [map_add, Finset.sum_add_distrib]

@[simp] theorem bilinearProduct_add_right (f : A →ₗ[ℂ] A →ₗ[ℂ] A) {p r q : ℕ}
    (X : CStarMatrix (Fin p) (Fin r) A) (Y Y' : CStarMatrix (Fin r) (Fin q) A) :
    bilinearProduct f X (Y + Y') = bilinearProduct f X Y + bilinearProduct f X Y' := by
  ext i j
  simp [map_add, Finset.sum_add_distrib]

@[simp] theorem bilinearProduct_smul (z : ℂ) (f : A →ₗ[ℂ] A →ₗ[ℂ] A) {p r q : ℕ}
    (X : CStarMatrix (Fin p) (Fin r) A) (Y : CStarMatrix (Fin r) (Fin q) A) :
    bilinearProduct (z • f) X Y = z • bilinearProduct f X Y := by
  ext i j
  change (∑ k, z • f (X i k) (Y k j)) = z • ∑ k, f (X i k) (Y k j)
  rw [Finset.smul_sum]

/-- Algebraic associativity survives every rectangular matrix amplification. -/
theorem bilinearProduct_assoc (m : A →ₗ[ℂ] A →ₗ[ℂ] A)
    (hm : ∀ x y z, m (m x y) z = m x (m y z)) {p r s q : ℕ}
    (X : CStarMatrix (Fin p) (Fin r) A) (Y : CStarMatrix (Fin r) (Fin s) A)
    (Z : CStarMatrix (Fin s) (Fin q) A) :
    bilinearProduct m (bilinearProduct m X Y) Z =
      bilinearProduct m X (bilinearProduct m Y Z) := by
  ext i l
  simp only [bilinearProduct_apply, map_sum, LinearMap.sum_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => hm _ _ _

theorem rectangular_mul_assoc {p r s q : ℕ}
    (X : CStarMatrix (Fin p) (Fin r) A) (Y : CStarMatrix (Fin r) (Fin s) A)
    (Z : CStarMatrix (Fin s) (Fin q) A) : (X * Y) * Z = X * (Y * Z) := by
  ext i l
  change (∑ k, (∑ j, X i j * Y j k) * Z k l) =
    ∑ j, X i j * (∑ k, Y j k * Z k l)
  simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

/-- The degree-two Hochschild differential, already amplified to matrices. -/
def matrixBilinearDifferential (f : A →ₗ[ℂ] A →ₗ[ℂ] A) {p r s q : ℕ}
    (X : CStarMatrix (Fin p) (Fin r) A) (Y : CStarMatrix (Fin r) (Fin s) A)
    (Z : CStarMatrix (Fin s) (Fin q) A) : CStarMatrix (Fin p) (Fin q) A :=
  X * bilinearProduct f Y Z - bilinearProduct f (X * Y) Z +
    bilinearProduct f X (Y * Z) - bilinearProduct f X Y * Z

/-- The Maurer--Cartan identity, with its signs fixed for the correction step. -/
theorem matrixBilinearDifferential_defect (m : A →ₗ[ℂ] A →ₗ[ℂ] A)
    (hm : ∀ x y z, m (m x y) z = m x (m y z)) {p r s q : ℕ}
    (X : CStarMatrix (Fin p) (Fin r) A) (Y : CStarMatrix (Fin r) (Fin s) A)
    (Z : CStarMatrix (Fin s) (Fin q) A) :
    let f := m - LinearMap.mul ℂ A
    matrixBilinearDifferential f X Y Z =
      bilinearProduct f (bilinearProduct f X Y) Z -
        bilinearProduct f X (bilinearProduct f Y Z) := by
  let f := m - LinearMap.mul ℂ A
  have hm' : m = LinearMap.mul ℂ A + f := by dsimp [f]; abel
  have he := bilinearProduct_assoc m hm X Y Z
  rw [hm'] at he
  simp only [bilinearProduct_add, bilinearProduct_mul, bilinearProduct_add_left,
    bilinearProduct_add_right, rectangular_mul_assoc] at he
  dsimp only [matrixBilinearDifferential]
  change X * bilinearProduct f Y Z - bilinearProduct f (X * Y) Z +
      bilinearProduct f X (Y * Z) - bilinearProduct f X Y * Z = _
  have he' := congrArg (fun T => T - (X * Y) * Z -
    bilinearProduct f (X * Y) Z - bilinearProduct f X Y * Z -
    bilinearProduct f X (bilinearProduct f Y Z)) he
  rw [← rectangular_mul_assoc] at he'
  symm
  convert he' using 1 <;> abel

variable [PartialOrder A] [StarOrderedRing A]

theorem HaagerupBound.add {f g : A →ₗ[ℂ] A →ₗ[ℂ] A} {c d : ℝ}
    (hf : HaagerupBound f c) (hg : HaagerupBound g d) : HaagerupBound (f + g) (c + d) := by
  intro p r q X Y
  rw [bilinearProduct_add]
  calc
    _ ≤ ‖bilinearProduct f X Y‖ + ‖bilinearProduct g X Y‖ := norm_add_le _ _
    _ ≤ c * ‖X‖ * ‖Y‖ + d * ‖X‖ * ‖Y‖ := add_le_add (hf p r q X Y) (hg p r q X Y)
    _ = _ := by ring

theorem HaagerupBound.smul {f : A →ₗ[ℂ] A →ₗ[ℂ] A} {c : ℝ}
    (hf : HaagerupBound f c) (z : ℂ) : HaagerupBound (z • f) (‖z‖ * c) := by
  intro p r q X Y
  rw [bilinearProduct_smul, norm_smul]
  exact (mul_le_mul_of_nonneg_left (hf p r q X Y) (norm_nonneg z)).trans_eq (by ring)

/-- A defect bounded by q has differential bounded by 2q², uniformly in
all four matrix dimensions. -/
theorem matrixBilinearDifferential_defect_bound
    (m : A →ₗ[ℂ] A →ₗ[ℂ] A)
    (hm : ∀ x y z, m (m x y) z = m x (m y z)) {c : ℝ} (hc : 0 ≤ c)
    (hf : HaagerupBound (m - LinearMap.mul ℂ A) c) {p r s q : ℕ}
    (X : CStarMatrix (Fin p) (Fin r) A) (Y : CStarMatrix (Fin r) (Fin s) A)
    (Z : CStarMatrix (Fin s) (Fin q) A) :
    ‖matrixBilinearDifferential (m - LinearMap.mul ℂ A) X Y Z‖ ≤
      2 * c ^ 2 * ‖X‖ * ‖Y‖ * ‖Z‖ := by
  rw [matrixBilinearDifferential_defect m hm]
  calc
    _ ≤ ‖bilinearProduct (m - LinearMap.mul ℂ A)
          (bilinearProduct (m - LinearMap.mul ℂ A) X Y) Z‖ +
        ‖bilinearProduct (m - LinearMap.mul ℂ A) X
          (bilinearProduct (m - LinearMap.mul ℂ A) Y Z)‖ := norm_sub_le _ _
    _ ≤ c * (c * ‖X‖ * ‖Y‖) * ‖Z‖ + c * ‖X‖ * (c * ‖Y‖ * ‖Z‖) := by
      apply add_le_add
      · exact (hf p s q _ Z).trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hf p r s X Y) hc) (norm_nonneg Z))
      · exact (hf p r q X _).trans (mul_le_mul_of_nonneg_left
          (hf r s q Y Z) (mul_nonneg hc (norm_nonneg X)))
    _ = _ := by ring

end

end KadisonKastler

end OAI
