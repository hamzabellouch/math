import OAI.Analysis.KadisonKastler.Multiplication
import OAI.Analysis.KadisonKastler.CorrectionBounds
import Mathlib.Analysis.CStarAlgebra.CStarMatrix

namespace OAI

/-!
# Matrix bounds for perturbation maps

All norms here are the C*-matrix norms, including for rectangular matrices.
The rectangular formulation records exactly the estimates needed for the
Haagerup product norm in the multiplication-correction argument.
-/

namespace KadisonKastler

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder A] [StarOrderedRing A] in
theorem rectangular_toCLM_mul {p r q : ℕ}
    (X : CStarMatrix (Fin p) (Fin r) A) (Y : CStarMatrix (Fin r) (Fin q) A) :
    CStarMatrix.toCLM (X * Y) = (CStarMatrix.toCLM Y).comp (CStarMatrix.toCLM X) := by
  ext v i
  simp only [CStarMatrix.toCLM_apply, ContinuousLinearMap.comp_apply]
  exact congrFun (Matrix.vecMul_vecMul v X Y).symm i

/-- Submultiplicativity also holds for rectangular C*-matrices. -/
theorem rectangular_norm_mul_le {p r q : ℕ}
    (X : CStarMatrix (Fin p) (Fin r) A) (Y : CStarMatrix (Fin r) (Fin q) A) :
    ‖X * Y‖ ≤ ‖X‖ * ‖Y‖ := by
  simp only [CStarMatrix.norm_def, rectangular_toCLM_mul]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans_eq (mul_comm _ _)

/-- A complete bound, expressed on all finite rectangular matrix levels. -/
def CompletelyBoundedBy (F : A →ₗ[ℂ] B) (c : ℝ) : Prop :=
  ∀ (p q : ℕ) (X : CStarMatrix (Fin p) (Fin q) A),
    ‖CStarMatrix.mapₗ F X‖ ≤ c * ‖X‖

/-- Complete isometry in the same rectangular convention. -/
def CompletelyIsometric (F : A →ₗ[ℂ] B) : Prop :=
  ∀ (p q : ℕ) (X : CStarMatrix (Fin p) (Fin q) A),
    ‖CStarMatrix.mapₗ F X‖ = ‖X‖

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
/-- Entrywise application of a linear equivalence is an equivalence at
every rectangular matrix size. -/
def matrixLinearEquiv (F : A ≃ₗ[ℂ] B) (p q : ℕ) :
    CStarMatrix (Fin p) (Fin q) A ≃ₗ[ℂ] CStarMatrix (Fin p) (Fin q) B where
  toFun := CStarMatrix.mapₗ F.toLinearMap
  invFun := CStarMatrix.mapₗ F.symm.toLinearMap
  left_inv X := by ext i j; exact F.symm_apply_apply (X i j)
  right_inv X := by ext i j; exact F.apply_symm_apply (X i j)
  map_add' := map_add _
  map_smul' := map_smul _

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
theorem matrixLinearEquiv_symm_apply (F : A ≃ₗ[ℂ] B) (p q : ℕ)
    (X : CStarMatrix (Fin p) (Fin q) B) :
    (matrixLinearEquiv F p q).symm X = CStarMatrix.mapₗ F.symm.toLinearMap X := rfl

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
theorem matrix_map_sub (F G : A →ₗ[ℂ] B) {p q : ℕ}
    (X : CStarMatrix (Fin p) (Fin q) A) :
    CStarMatrix.mapₗ (F - G) X = CStarMatrix.mapₗ F X - CStarMatrix.mapₗ G X := by
  ext i j
  rfl

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
theorem matrix_map_mul (ρ : A →ₐ[ℂ] B) {p r q : ℕ}
    (X : CStarMatrix (Fin p) (Fin r) A) (Y : CStarMatrix (Fin r) (Fin q) A) :
    CStarMatrix.mapₗ ρ.toLinearMap (X * Y) =
      CStarMatrix.mapₗ ρ.toLinearMap X * CStarMatrix.mapₗ ρ.toLinearMap Y := by
  ext i k
  simp [CStarMatrix.mul_apply, CStarMatrix.mapₗ_apply, CStarMatrix.map_apply, map_sum]

/-- The multiplicative defect estimate at all rectangular matrix sizes.
This is the estimate used before transporting multiplication through `F`. -/
theorem matrix_multiplicative_defect_le
    (ρ : A →ₐ[ℂ] B) (F : A →ₗ[ℂ] B) {e : ℝ} (he : 0 ≤ e)
    (hρ : CompletelyIsometric ρ.toLinearMap)
    (hF : CompletelyBoundedBy F 1)
    (hclose : CompletelyBoundedBy (F - ρ.toLinearMap) e)
    {p r q : ℕ} (X : CStarMatrix (Fin p) (Fin r) A)
    (Y : CStarMatrix (Fin r) (Fin q) A) :
    ‖CStarMatrix.mapₗ F (X * Y) - CStarMatrix.mapₗ F X * CStarMatrix.mapₗ F Y‖ ≤
      3 * e * ‖X‖ * ‖Y‖ := by
  have hclose' {m n : ℕ} (Z : CStarMatrix (Fin m) (Fin n) A) :
      ‖CStarMatrix.mapₗ F Z - CStarMatrix.mapₗ ρ.toLinearMap Z‖ ≤ e * ‖Z‖ := by
    simpa only [matrix_map_sub] using hclose m n Z
  have hexpand :
      CStarMatrix.mapₗ F (X * Y) - CStarMatrix.mapₗ F X * CStarMatrix.mapₗ F Y =
      (CStarMatrix.mapₗ F (X * Y) - CStarMatrix.mapₗ ρ.toLinearMap (X * Y)) +
      (CStarMatrix.mapₗ ρ.toLinearMap X - CStarMatrix.mapₗ F X) *
        CStarMatrix.mapₗ ρ.toLinearMap Y +
      CStarMatrix.mapₗ F X *
        (CStarMatrix.mapₗ ρ.toLinearMap Y - CStarMatrix.mapₗ F Y) := by
    rw [matrix_map_mul]
    ext i k
    simp only [CStarMatrix.add_apply, CStarMatrix.sub_apply, CStarMatrix.mul_apply,
      sub_mul, mul_sub, Finset.sum_sub_distrib]
    abel
  rw [hexpand]
  calc
    _ ≤ ‖CStarMatrix.mapₗ F (X * Y) - CStarMatrix.mapₗ ρ.toLinearMap (X * Y)‖ +
        ‖(CStarMatrix.mapₗ ρ.toLinearMap X - CStarMatrix.mapₗ F X) *
          CStarMatrix.mapₗ ρ.toLinearMap Y‖ +
        ‖CStarMatrix.mapₗ F X *
          (CStarMatrix.mapₗ ρ.toLinearMap Y - CStarMatrix.mapₗ F Y)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ e * (‖X‖ * ‖Y‖) + (e * ‖X‖) * ‖Y‖ + ‖X‖ * (e * ‖Y‖) := by
      apply add_le_add
      · apply add_le_add
        · exact (hclose' _).trans (mul_le_mul_of_nonneg_left
            (rectangular_norm_mul_le X Y) he)
        · refine (rectangular_norm_mul_le _ _).trans ?_
          rw [hρ r q Y, norm_sub_rev]
          exact mul_le_mul_of_nonneg_right (hclose' X) (norm_nonneg Y)
      · refine (rectangular_norm_mul_le _ _).trans ?_
        rw [norm_sub_rev]
        exact mul_le_mul (by simpa using hF p r X) (hclose' Y)
          (norm_nonneg _) (norm_nonneg _)
    _ = 3 * e * ‖X‖ * ‖Y‖ := by ring

/-- The row-column defect of the transported multiplication. This is the
concrete inequality used to invoke the published multiplication theorem. -/
def TransportedProductBound (F : A ≃ₗ[ℂ] B) (c : ℝ) : Prop :=
  ∀ (p r q : ℕ) (X : CStarMatrix (Fin p) (Fin r) A)
      (Y : CStarMatrix (Fin r) (Fin q) A),
    ‖CStarMatrix.mapₗ F.symm.toLinearMap
        (CStarMatrix.mapₗ F.toLinearMap X * CStarMatrix.mapₗ F.toLinearMap Y) -
        X * Y‖ ≤ c * ‖X‖ * ‖Y‖

theorem transportedProductBound_of_defect (F : A ≃ₗ[ℂ] B) {K c : ℝ}
    (hK : 0 ≤ K) (hinv : CompletelyBoundedBy F.symm.toLinearMap K)
    (hdefect : ∀ (p r q : ℕ) (X : CStarMatrix (Fin p) (Fin r) A)
        (Y : CStarMatrix (Fin r) (Fin q) A),
      ‖CStarMatrix.mapₗ F.toLinearMap (X * Y) -
          CStarMatrix.mapₗ F.toLinearMap X * CStarMatrix.mapₗ F.toLinearMap Y‖ ≤
        c * ‖X‖ * ‖Y‖) :
    TransportedProductBound F (K * c) := by
  intro p r q X Y
  have hid : CStarMatrix.mapₗ F.symm.toLinearMap
      (CStarMatrix.mapₗ F.toLinearMap (X * Y)) = X * Y := by
    ext i j
    exact F.symm_apply_apply _
  rw [← hid, ← map_sub]
  exact (hinv p q _).trans (by
    rw [norm_sub_rev]
    calc
      K * ‖CStarMatrix.mapₗ F.toLinearMap (X * Y) -
          CStarMatrix.mapₗ F.toLinearMap X * CStarMatrix.mapₗ F.toLinearMap Y‖ ≤
          K * (c * ‖X‖ * ‖Y‖) :=
        mul_le_mul_of_nonneg_left (hdefect p r q X Y) hK
      _ = (K * c) * ‖X‖ * ‖Y‖ := by ring)

theorem inverse_completelyBoundedBy_of_close_to_id (L : A ≃ₗ[ℂ] A)
    {η : ℝ} (hη : η < 1)
    (hclose : CompletelyBoundedBy (L.toLinearMap - LinearMap.id) η) :
    CompletelyBoundedBy L.symm.toLinearMap ((1 - η)⁻¹) := by
  intro p q X
  apply norm_inverse_le_of_close_to_id (matrixLinearEquiv L p q) hη
  intro Y
  have hid : CStarMatrix.mapₗ (LinearMap.id : A →ₗ[ℂ] A) Y = Y := by
    ext i j
    rfl
  have h := hclose p q Y
  rw [matrix_map_sub, hid] at h
  exact h

theorem inverse_sub_completelyBoundedBy_of_close_to_id (L : A ≃ₗ[ℂ] A)
    {η : ℝ} (hη₀ : 0 ≤ η) (hη : η < 1)
    (hclose : CompletelyBoundedBy (L.toLinearMap - LinearMap.id) η) :
    CompletelyBoundedBy (L.symm.toLinearMap - LinearMap.id) (η / (1 - η)) := by
  intro p q X
  rw [matrix_map_sub]
  apply norm_inverse_sub_le_of_close_to_id (matrixLinearEquiv L p q) hη₀ hη
  intro Y
  have hid : CStarMatrix.mapₗ (LinearMap.id : A →ₗ[ℂ] A) Y = Y := by
    ext i j
    rfl
  have h := hclose p q Y
  rw [matrix_map_sub, hid] at h
  exact h

end

end KadisonKastler

end OAI
