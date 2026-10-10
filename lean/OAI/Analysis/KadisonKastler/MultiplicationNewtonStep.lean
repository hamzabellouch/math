import OAI.Analysis.KadisonKastler.HaagerupCochains
import OAI.Analysis.KadisonKastler.MatrixCorrection

namespace OAI

/-! # One quadratic step in correction of multiplication

These are the concrete matrix identities used in the perturbation iteration.
The choice of a correcting cochain is a separate construction.
-/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

/-- The Hochschild coboundary of a linear cochain. -/
def linearCoboundary (D : A →ₗ[ℂ] A) : A →ₗ[ℂ] A →ₗ[ℂ] A where
  toFun x := (LinearMap.mul ℂ A x).comp D - D.comp (LinearMap.mul ℂ A x) +
    LinearMap.mul ℂ A (D x)
  map_add' x y := by
    ext z
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.mul_apply', map_add]
    abel
  map_smul' c x := by
    ext z
    simp [smul_sub, smul_add]

@[simp] theorem linearCoboundary_apply (D : A →ₗ[ℂ] A) (x y : A) :
    linearCoboundary D x y = x * D y - D (x * y) + D x * y := rfl

/-- The coboundary formula is unchanged at every rectangular matrix level. -/
theorem bilinearProduct_linearCoboundary (D : A →ₗ[ℂ] A) {p r q : ℕ}
    (X : CStarMatrix (Fin p) (Fin r) A) (Y : CStarMatrix (Fin r) (Fin q) A) :
    bilinearProduct (linearCoboundary D) X Y =
      X * CStarMatrix.mapₗ D Y - CStarMatrix.mapₗ D (X * Y) +
        CStarMatrix.mapₗ D X * Y := by
  ext i j
  simp [CStarMatrix.mul_apply, map_sum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]

/-- Transport an arbitrary bilinear multiplication by a linear equivalence. -/
def conjugatedBilinear (L : A ≃ₗ[ℂ] A) (m : A →ₗ[ℂ] A →ₗ[ℂ] A) :
    A →ₗ[ℂ] A →ₗ[ℂ] A where
  toFun x := L.toLinearMap.comp ((m (L.symm x)).comp L.symm.toLinearMap)
  map_add' x y := by ext z; simp
  map_smul' c x := by ext z; simp

@[simp] theorem conjugatedBilinear_apply (L : A ≃ₗ[ℂ] A)
    (m : A →ₗ[ℂ] A →ₗ[ℂ] A) (x y : A) :
    conjugatedBilinear L m x y = L (m (L.symm x) (L.symm y)) := rfl

theorem bilinearProduct_conjugated (L : A ≃ₗ[ℂ] A)
    (m : A →ₗ[ℂ] A →ₗ[ℂ] A) {p r q : ℕ}
    (X : CStarMatrix (Fin p) (Fin r) A) (Y : CStarMatrix (Fin r) (Fin q) A) :
    bilinearProduct (conjugatedBilinear L m) X Y =
      CStarMatrix.mapₗ L.toLinearMap
        (bilinearProduct m (CStarMatrix.mapₗ L.symm.toLinearMap X)
          (CStarMatrix.mapₗ L.symm.toLinearMap Y)) := by
  ext i j
  simp [map_sum]

theorem conjugatedBilinear_assoc (L : A ≃ₗ[ℂ] A)
    (m : A →ₗ[ℂ] A →ₗ[ℂ] A) (hm : ∀ x y z, m (m x y) z = m x (m y z)) :
    ∀ x y z, conjugatedBilinear L m (conjugatedBilinear L m x y) z =
      conjugatedBilinear L m x (conjugatedBilinear L m y z) := by
  intro x y z
  simp only [conjugatedBilinear_apply, L.symm_apply_apply, hm]

theorem conjugatedBilinear_star (L : A ≃ₗ[ℂ] A)
    (hL : ∀ x, L (star x) = star (L x))
    (m : A →ₗ[ℂ] A →ₗ[ℂ] A)
    (hm : ∀ x y, star (m x y) = m (star y) (star x)) :
    ∀ x y, star (conjugatedBilinear L m x y) =
      conjugatedBilinear L m (star y) (star x) := by
  have hinv (x : A) : L.symm (star x) = star (L.symm x) := by
    apply L.injective
    simp [hL]
  intro x y
  simp only [conjugatedBilinear_apply, ← hL, hm, hinv]

/-- Exact error before conjugating by the near-identity correction. -/
theorem matrix_newton_residual (m : A →ₗ[ℂ] A →ₗ[ℂ] A) (D : A →ₗ[ℂ] A)
    {p r q : ℕ} (X : CStarMatrix (Fin p) (Fin r) A)
    (Y : CStarMatrix (Fin r) (Fin q) A) :
    CStarMatrix.mapₗ (LinearMap.id + D) (bilinearProduct m X Y) -
      CStarMatrix.mapₗ (LinearMap.id + D) X * CStarMatrix.mapₗ (LinearMap.id + D) Y =
    bilinearProduct (m - LinearMap.mul ℂ A - linearCoboundary D) X Y +
      CStarMatrix.mapₗ D (bilinearProduct (m - LinearMap.mul ℂ A) X Y) -
      CStarMatrix.mapₗ D X * CStarMatrix.mapₗ D Y := by
  have hadd {p q : ℕ} (Z : CStarMatrix (Fin p) (Fin q) A) :
      CStarMatrix.mapₗ (LinearMap.id + D) Z = Z + CStarMatrix.mapₗ D Z := by
    ext i j
    rfl
  simp only [hadd, bilinearProduct_sub, bilinearProduct_mul,
    bilinearProduct_linearCoboundary, map_sub, CStarMatrix.add_mul, CStarMatrix.mul_add]
  abel

variable [PartialOrder A] [StarOrderedRing A]

/-- The new error is the uncorrected cohomology error plus two quadratic terms. -/
theorem matrix_newton_residual_bound (m : A →ₗ[ℂ] A →ₗ[ℂ] A) (D : A →ₗ[ℂ] A)
    {c q r : ℝ} (hc : 0 ≤ c)
    (hD : CompletelyBoundedBy D c)
    (hm : HaagerupBound (m - LinearMap.mul ℂ A) q)
    (hres : HaagerupBound (m - LinearMap.mul ℂ A - linearCoboundary D) r)
    {p s t : ℕ} (X : CStarMatrix (Fin p) (Fin s) A)
    (Y : CStarMatrix (Fin s) (Fin t) A) :
    ‖CStarMatrix.mapₗ (LinearMap.id + D) (bilinearProduct m X Y) -
      CStarMatrix.mapₗ (LinearMap.id + D) X * CStarMatrix.mapₗ (LinearMap.id + D) Y‖ ≤
      (r + c * q + c ^ 2) * ‖X‖ * ‖Y‖ := by
  rw [matrix_newton_residual]
  calc
    _ ≤ ‖bilinearProduct (m - LinearMap.mul ℂ A - linearCoboundary D) X Y‖ +
        ‖CStarMatrix.mapₗ D (bilinearProduct (m - LinearMap.mul ℂ A) X Y)‖ +
        ‖CStarMatrix.mapₗ D X * CStarMatrix.mapₗ D Y‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ r * ‖X‖ * ‖Y‖ + c * (q * ‖X‖ * ‖Y‖) +
        (c * ‖X‖) * (c * ‖Y‖) := by
      apply add_le_add
      · apply add_le_add (hres p s t X Y)
        exact (hD p t _).trans (mul_le_mul_of_nonneg_left (hm p s t X Y) hc)
      · exact (rectangular_norm_mul_le _ _).trans
          (mul_le_mul (hD p s X) (hD s t Y) (norm_nonneg _) (mul_nonneg hc (norm_nonneg X)))
    _ = _ := by ring

/-- After changing coordinates, the new multiplication has the same quadratic
bound divided by the two inverse-coordinate bounds. -/
theorem conjugatedBilinear_defect_bound
    (m : A →ₗ[ℂ] A →ₗ[ℂ] A) (D : A →ₗ[ℂ] A) (L : A ≃ₗ[ℂ] A)
    (hL : L.toLinearMap = LinearMap.id + D) {c q r : ℝ}
    (hc : 0 ≤ c) (hc1 : c < 1) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hD : CompletelyBoundedBy D c)
    (hm : HaagerupBound (m - LinearMap.mul ℂ A) q)
    (hres : HaagerupBound (m - LinearMap.mul ℂ A - linearCoboundary D) r) :
    HaagerupBound (conjugatedBilinear L m - LinearMap.mul ℂ A)
      ((r + c * q + c ^ 2) / (1 - c) ^ 2) := by
  have hclose : CompletelyBoundedBy (L.toLinearMap - LinearMap.id) c := by
    simpa only [hL, add_sub_cancel_left] using hD
  have hinv := inverse_completelyBoundedBy_of_close_to_id L hc1 hclose
  have hK : 0 ≤ r + c * q + c ^ 2 := by positivity
  have hinv0 : 0 ≤ (1 - c)⁻¹ := inv_nonneg.mpr (sub_pos.mpr hc1).le
  intro p s t X Y
  let U := CStarMatrix.mapₗ L.symm.toLinearMap X
  let V := CStarMatrix.mapₗ L.symm.toLinearMap Y
  have hU : CStarMatrix.mapₗ L.toLinearMap U = X := by
    ext i j
    exact L.apply_symm_apply _
  have hV : CStarMatrix.mapₗ L.toLinearMap V = Y := by
    ext i j
    exact L.apply_symm_apply _
  have herror : bilinearProduct (conjugatedBilinear L m - LinearMap.mul ℂ A) X Y =
      CStarMatrix.mapₗ (LinearMap.id + D) (bilinearProduct m U V) -
        CStarMatrix.mapₗ (LinearMap.id + D) U * CStarMatrix.mapₗ (LinearMap.id + D) V := by
    rw [bilinearProduct_sub, bilinearProduct_mul, bilinearProduct_conjugated]
    rw [← hL, hU, hV]
  rw [herror]
  calc
    _ ≤ (r + c * q + c ^ 2) * ‖U‖ * ‖V‖ :=
      matrix_newton_residual_bound m D hc hD hm hres U V
    _ ≤ (r + c * q + c ^ 2) * ((1 - c)⁻¹ * ‖X‖) * ((1 - c)⁻¹ * ‖Y‖) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (hinv p s X) hK
      · exact hinv s t Y
      · exact norm_nonneg V
      · positivity
    _ = ((r + c * q + c ^ 2) / (1 - c) ^ 2) * ‖X‖ * ‖Y‖ := by
      field_simp

end

end KadisonKastler

end OAI
