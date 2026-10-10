import OAI.Analysis.KadisonKastler.TracialCauchySchwarz

namespace OAI

/-! # Multiplication estimates for the tracial two-norm -/

namespace KadisonKastler

noncomputable section

universe u

variable {B : Type u} [CStarAlgebra B]

/-- Left multiplication costs at most the ambient operator norm. -/
theorem traceTwoNorm_mul_le_left (τ : FaithfulTracialState B) (x y : B) :
    traceTwoNorm τ (x * y) ≤ ‖x‖ * traceTwoNorm τ y := by
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  have hpos : 0 ≤ algebraMap ℝ B (‖x‖ ^ 2) - star x * x :=
    sub_nonneg.mpr (CStarAlgebra.star_mul_le_algebraMap_norm_sq x)
  obtain ⟨z, hz⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hpos
  have he : star (z * y) * (z * y) =
      (‖x‖ ^ 2 : ℂ) • (star y * y) - star (x * y) * (x * y) := by
    calc
      star (z * y) * (z * y) = star y * (star z * z) * y := by
        simp only [star_mul, mul_assoc]
      _ = star y * (algebraMap ℝ B (‖x‖ ^ 2) - star x * x) * y := by rw [hz]
      _ = (‖x‖ ^ 2 : ℂ) • (star y * y) - star (x * y) * (x * y) := by
        rw [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul]
        simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one,
          star_mul, mul_assoc]
        norm_cast
  have ht := τ.positive (z * y)
  rw [he, map_sub, map_smul, smul_eq_mul, Complex.sub_re] at ht
  have hr : ((‖x‖ ^ 2 : ℂ) * τ.toLinearMap (star y * y)).re =
      ‖x‖ ^ 2 * (τ.toLinearMap (star y * y)).re := by
    rw [← Complex.ofReal_pow]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [hr] at ht
  have hxy := traceTwoNorm_sq τ (x * y)
  have hy := traceTwoNorm_sq τ y
  have hn := mul_nonneg (norm_nonneg x) (traceTwoNorm_nonneg τ y)
  have hs : traceTwoNorm τ (x * y) ^ 2 ≤ (‖x‖ * traceTwoNorm τ y) ^ 2 := by
    rw [mul_pow, hxy, hy]
    linarith
  nlinarith [traceTwoNorm_nonneg τ (x * y)]

/-- Right multiplication has the corresponding operator-norm bound. -/
theorem traceTwoNorm_mul_le_right (τ : FaithfulTracialState B) (x y : B) :
    traceTwoNorm τ (x * y) ≤ traceTwoNorm τ x * ‖y‖ := by
  calc
    traceTwoNorm τ (x * y) = traceTwoNorm τ (star y * star x) := by
      rw [← star_mul, traceTwoNorm_star]
    _ ≤ ‖star y‖ * traceTwoNorm τ (star x) := traceTwoNorm_mul_le_left τ _ _
    _ = traceTwoNorm τ x * ‖y‖ := by rw [norm_star, traceTwoNorm_star, mul_comm]

/-- A unitary on the left preserves the tracial two-norm exactly. -/
@[simp]
theorem traceTwoNorm_unitary_mul (τ : FaithfulTracialState B) (u : unitary B) (x : B) :
    traceTwoNorm τ ((u : B) * x) = traceTwoNorm τ x := by
  have he : star ((u : B) * x) * ((u : B) * x) = star x * x := by
    rw [star_mul]
    calc
      star x * star (u : B) * ((u : B) * x) =
          star x * (star (u : B) * (u : B)) * x := by noncomm_ring
      _ = star x * x := by rw [Unitary.star_mul_self_of_mem u.property, mul_one]
  simp only [traceTwoNorm, he]

/-- A unitary on the right preserves the tracial two-norm by traciality. -/
@[simp]
theorem traceTwoNorm_mul_unitary (τ : FaithfulTracialState B) (u : unitary B) (x : B) :
    traceTwoNorm τ (x * (u : B)) = traceTwoNorm τ x := by
  calc
    traceTwoNorm τ (x * (u : B)) = traceTwoNorm τ (star (u : B) * star x) := by
      rw [← star_mul, traceTwoNorm_star]
    _ = traceTwoNorm τ (star x) := by
      exact traceTwoNorm_unitary_mul τ (star u) (star x)
    _ = traceTwoNorm τ x := traceTwoNorm_star τ x

end

end KadisonKastler

end OAI
