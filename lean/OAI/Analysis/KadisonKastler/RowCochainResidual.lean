import OAI.Analysis.KadisonKastler.FiniteRowCochains
import OAI.Analysis.KadisonKastler.FiniteCochainDifferential

namespace OAI

/-! The finite-row residual has a quadratic bound after removing its module defect. -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

/-- Failure of the finite average to be a right module map in its last argument. -/
def finiteCochainModuleDefect {κ : Type*} [Fintype κ] (r : κ → A)
    (f : A →ₗ[ℂ] A →ₗ[ℂ] A) : A →ₗ[ℂ] A →ₗ[ℂ] A :=
  (finiteRightAverage r).comp f - (LinearMap.mul ℂ A).comp (finiteCochainAverage r f)

/-- The averaged differential, written as an actual bilinear map. -/
def finiteAveragedDifferential {κ : Type*} [Fintype κ] (r : κ → A)
    (f : A →ₗ[ℂ] A →ₗ[ℂ] A) : A →ₗ[ℂ] A →ₗ[ℂ] A :=
  finiteCochainModuleDefect r f - (f - linearCoboundary (finiteCochainAverage r f))

theorem finiteAveragedDifferential_apply {κ : Type*} [Fintype κ] (r : κ → A)
    (hr : ∑ k, r k * star (r k) = 1) (f : A →ₗ[ℂ] A →ₗ[ℂ] A) (x y : A) :
    finiteAveragedDifferential r f x y =
      ∑ k, cochainDifferential f x y (r k) * star (r k) := by
  have h := finiteCochainAverage_residual r hr f x y
  change (finiteRightAverage r (f x) y - finiteCochainAverage r f x * y) -
    (f x y - linearCoboundary (finiteCochainAverage r f) x y) = _
  rw [h]
  abel

theorem cochainDifferential_zero (f : A →ₗ[ℂ] A →ₗ[ℂ] A) (x y : A) :
    cochainDifferential f x y 0 = 0 := by simp [cochainDifferential]

theorem finiteMatrixDifferential_apply (f : A →ₗ[ℂ] A →ₗ[ℂ] A)
    {p r s q : Type*} [Fintype r] [Fintype s]
    (X : CStarMatrix p r A) (Y : CStarMatrix r s A) (Z : CStarMatrix s q A)
    (i : p) (l : q) :
    finiteMatrixDifferential f X Y Z i l =
      ∑ j, ∑ k, cochainDifferential f (X i j) (Y j k) (Z k l) := by
  simp only [finiteMatrixDifferential, CStarMatrix.sub_apply, CStarMatrix.add_apply,
    CStarMatrix.mul_apply, finiteBilinearProduct_apply, map_sum, LinearMap.sum_apply,
    Finset.mul_sum, Finset.sum_mul, cochainDifferential, Finset.sum_sub_distrib,
    Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun k j => f (X i j * Y j k) (Z k l)),
    Finset.sum_comm (f := fun k j => f (X i j) (Y j k) * Z k l)]

/-- Exact matrix identity for the averaged Hochschild differential. -/
theorem finiteAveragedDifferential_matrix {κ : Type*} [Fintype κ]
    (r : κ → A) (hr : ∑ k, r k * star (r k) = 1)
    (f : A →ₗ[ℂ] A →ₗ[ℂ] A) {p t q : ℕ}
    (X : CStarMatrix (Fin p) (Fin t) A) (Y : CStarMatrix (Fin t) (Fin q) A) :
    bilinearProduct (finiteAveragedDifferential r f) X Y =
      finiteMatrixDifferential f X Y (rowReplication r) * (rowReplication r).conjTranspose := by
  ext i j
  simp only [bilinearProduct_apply, finiteAveragedDifferential_apply r hr,
    CStarMatrix.mul_apply, CStarMatrix.conjTranspose_apply, finiteMatrixDifferential_apply,
    Fintype.sum_prod_type, rowReplication_apply]
  simp_rw [apply_ite]
  simp only [star_zero, cochainDifferential_zero, mul_zero,
    Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]


variable [PartialOrder A] [StarOrderedRing A]

/-- Averaging the differential of an associative multiplication defect
costs at most twice the square of its complete norm. -/
theorem finiteAveragedDifferential_defect_bound {κ : Type*} [Fintype κ]
    (r : κ → A) (hr : ∑ k, r k * star (r k) = 1)
    (m : A →ₗ[ℂ] A →ₗ[ℂ] A) (hm : ∀ x y z, m (m x y) z = m x (m y z))
    {c : ℝ} (hc : 0 ≤ c) (hf : HaagerupBound (m - LinearMap.mul ℂ A) c) :
    HaagerupBound (finiteAveragedDifferential r (m - LinearMap.mul ℂ A)) (2 * c ^ 2) := by
  intro p t q X Y
  have hb := rowReplication_norm_bounds (ι := Fin q) r hr
  rw [finiteAveragedDifferential_matrix r hr]
  calc
    _ ≤ ‖finiteMatrixDifferential (m - LinearMap.mul ℂ A) X Y (rowReplication r)‖ *
        ‖(rowReplication r).conjTranspose‖ := rectangular_norm_mul_le_finite _ _
    _ ≤ (2 * c ^ 2 * ‖X‖ * ‖Y‖ * ‖rowReplication r‖) *
        ‖(rowReplication r).conjTranspose‖ :=
      mul_le_mul_of_nonneg_right
        (finiteMatrixDifferential_defect_bound m hm hc hf X Y _) (norm_nonneg _)
    _ ≤ 2 * c ^ 2 * ‖X‖ * ‖Y‖ := by
      calc
        _ ≤ (2 * c ^ 2 * ‖X‖ * ‖Y‖ * 1) * 1 := by gcongr; exacts [hb.1, hb.2]
        _ = _ := by ring

end

end KadisonKastler

end OAI
