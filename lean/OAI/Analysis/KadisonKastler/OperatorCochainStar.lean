import OAI.Analysis.KadisonKastler.OperatorCochainColumn
import OAI.Analysis.KadisonKastler.RectangularOperator
import OAI.Analysis.KadisonKastler.MultiplicationNewtonStep

namespace OAI

/-! # Involution symmetrization of operator-valued cochains -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

def cochainSharp (D : A →ₗ[ℂ] A) : A →ₗ[ℂ] A where
  toFun x := star (D (star x))
  map_add' x y := by simp
  map_smul' c x := by simp

@[simp] theorem cochainSharp_apply (D : A →ₗ[ℂ] A) (x : A) :
    cochainSharp D x = star (D (star x)) := rfl

def bilinearSharp (f : A →ₗ[ℂ] A →ₗ[ℂ] A) : A →ₗ[ℂ] A →ₗ[ℂ] A where
  toFun x :=
    { toFun := fun y => star (f (star y) (star x))
      map_add' y z := by simp
      map_smul' c y := by simp }
  map_add' x y := by ext z; simp
  map_smul' c x := by ext z; simp

@[simp] theorem bilinearSharp_apply (f : A →ₗ[ℂ] A →ₗ[ℂ] A) (x y : A) :
    bilinearSharp f x y = star (f (star y) (star x)) := rfl

theorem matrix_cochainSharp (D : A →ₗ[ℂ] A) {p q : ℕ}
    (X : CStarMatrix (Fin p) (Fin q) A) :
    CStarMatrix.mapₗ (cochainSharp D) X =
      (CStarMatrix.mapₗ D X.conjTranspose).conjTranspose := by
  ext i j
  rfl

theorem matrix_bilinearSharp (f : A →ₗ[ℂ] A →ₗ[ℂ] A) {p r q : ℕ}
    (X : CStarMatrix (Fin p) (Fin r) A) (Y : CStarMatrix (Fin r) (Fin q) A) :
    bilinearProduct (bilinearSharp f) X Y =
      (bilinearProduct f Y.conjTranspose X.conjTranspose).conjTranspose := by
  ext i j
  simp [star_sum]

theorem bilinearSharp_coboundary (D : A →ₗ[ℂ] A) :
    bilinearSharp (linearCoboundary D) = linearCoboundary (cochainSharp D) := by
  ext x y
  simp only [bilinearSharp_apply, linearCoboundary_apply, cochainSharp_apply,
    star_add, star_sub, star_mul, star_star]
  abel

@[simp] theorem bilinearSharp_sub (f g : A →ₗ[ℂ] A →ₗ[ℂ] A) :
    bilinearSharp (f - g) = bilinearSharp f - bilinearSharp g := by
  ext x y
  simp

def cochainSymmetrize (D : A →ₗ[ℂ] A) : A →ₗ[ℂ] A :=
  (1/2 : ℂ) • (D + cochainSharp D)

theorem cochainSymmetrize_star (D : A →ₗ[ℂ] A) (x : A) :
    cochainSymmetrize D (star x) = star (cochainSymmetrize D x) := by
  simp [cochainSymmetrize, star_add, add_comm]

theorem cochainSymmetrize_residual (f : A →ₗ[ℂ] A →ₗ[ℂ] A)
    (hstar : ∀ x y, star (f x y) = f (star y) (star x)) (D : A →ₗ[ℂ] A) :
    f - linearCoboundary (cochainSymmetrize D) = (1/2 : ℂ) •
      ((f - linearCoboundary D) + bilinearSharp (f - linearCoboundary D)) := by
  have hs : bilinearSharp f = f := by
    ext x y
    simpa using hstar (star y) (star x)
  have hl : linearCoboundary (cochainSymmetrize D) = (1/2 : ℂ) •
      (linearCoboundary D + linearCoboundary (cochainSharp D)) := by
    ext x y
    simp only [linearCoboundary_apply, cochainSymmetrize, LinearMap.smul_apply,
      LinearMap.add_apply, smul_add, mul_smul_comm, smul_mul_assoc, mul_add, add_mul]
    module
  rw [hl, bilinearSharp_sub, hs, bilinearSharp_coboundary]
  module

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance cochainStarOperatorOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance cochainStarOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) := CStarAlgebra.spectralOrderedRing _

theorem operator_cochainSharp_bound {D : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H)} {c : ℝ}
    (hD : CompletelyBoundedBy D c) : CompletelyBoundedBy (cochainSharp D) c := by
  intro p q X
  rw [matrix_cochainSharp, norm_rectangular_star]
  simpa only [norm_rectangular_star] using hD q p X.conjTranspose

theorem operator_bilinearSharp_bound
    {f : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H)} {c : ℝ}
    (hf : HaagerupBound f c) : HaagerupBound (bilinearSharp f) c := by
  intro p r q X Y
  rw [matrix_bilinearSharp, norm_rectangular_star]
  have h := hf q r p Y.conjTranspose X.conjTranspose
  simpa only [norm_rectangular_star, mul_assoc, mul_comm, mul_left_comm] using h

theorem operator_cochainSymmetrize_bound
    {D : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H)} {c : ℝ}
    (hD : CompletelyBoundedBy D c) : CompletelyBoundedBy (cochainSymmetrize D) c := by
  intro p q X
  have he : CStarMatrix.mapₗ (cochainSymmetrize D) X =
      (1/2 : ℂ) • (CStarMatrix.mapₗ D X + CStarMatrix.mapₗ (cochainSharp D) X) := by
    ext i j
    rfl
  rw [he, norm_smul]
  norm_num only [norm_div, norm_one, Complex.norm_ofNat]
  calc
    (1/2 : ℝ) * ‖CStarMatrix.mapₗ D X + CStarMatrix.mapₗ (cochainSharp D) X‖ ≤
        (1/2 : ℝ) * (c * ‖X‖ + c * ‖X‖) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact (norm_add_le _ _).trans (add_le_add (hD p q X) (operator_cochainSharp_bound hD p q X))
    _ = _ := by ring

theorem operator_cochainSymmetrize_residual_bound
    {f : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H)}
    (hstar : ∀ x y, star (f x y) = f (star y) (star x))
    (D : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H)) {c : ℝ}
    (hres : HaagerupBound (f - linearCoboundary D) c) :
    HaagerupBound (f - linearCoboundary (cochainSymmetrize D)) c := by
  rw [cochainSymmetrize_residual f hstar D]
  have h := (hres.add (operator_bilinearSharp_bound hres)).smul (1/2 : ℂ)
  convert h using 1
  norm_num
  ring


end

end KadisonKastler

end OAI
