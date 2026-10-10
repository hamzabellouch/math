import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.ScaledDetectorProfile
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.EuclideanDerivativeBounds

namespace OAI

/-! Euclidean first and second derivative bounds for the injected bump.
The constant is a fixed, computed natural number, independent of its width. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows
open scoped ContDiff

def euclideanCoordinate (i : Fin 2) : EuclideanPlane →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp planeCoordinates.toContinuousLinearMap

theorem euclideanCoordinate_apply (i : Fin 2) (x : EuclideanPlane) :
    euclideanCoordinate i x = x i := rfl

theorem euclideanCoordinate_norm (i : Fin 2) : ‖euclideanCoordinate i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simpa only [euclideanCoordinate_apply, one_mul] using PiLp.norm_apply_le x i

theorem coordinateProfile_fderiv {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (i : Fin 2) (x : EuclideanPlane) :
    fderiv ℝ (fun y : EuclideanPlane => g (y i)) x =
      deriv g (x i) • euclideanCoordinate i := by
  have hd := ((hg.differentiable (by simp) (x i)).hasDerivAt).comp_hasFDerivAt x
    (euclideanCoordinate i).hasFDerivAt
  exact hd.fderiv

theorem coordinateProfile_second_fderiv {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (i : Fin 2) (x : EuclideanPlane) :
    fderiv ℝ (fderiv ℝ (fun y : EuclideanPlane => g (y i))) x =
      (deriv (deriv g) (x i) • euclideanCoordinate i).smulRight
        (euclideanCoordinate i) := by
  have he : fderiv ℝ (fun y : EuclideanPlane => g (y i)) =
      fun y => deriv g (y i) • euclideanCoordinate i := by
    funext y
    exact coordinateProfile_fderiv hg i y
  rw [he]
  have hg' : ContDiff ℝ ∞ (deriv g) := (contDiff_infty_iff_deriv.mp hg).2
  have hd := (((hg'.differentiable (by simp) (x i)).hasDerivAt).comp_hasFDerivAt x
    (euclideanCoordinate i).hasFDerivAt).smul_const (euclideanCoordinate i)
  exact hd.fderiv

theorem scalarProduct_second_fderiv {f g : EuclideanPlane → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : EuclideanPlane) :
    fderiv ℝ (fderiv ℝ (fun y => f y * g y)) x =
      (f x • fderiv ℝ (fderiv ℝ g) x +
        (fderiv ℝ f x).smulRight (fderiv ℝ g x)) +
      (g x • fderiv ℝ (fderiv ℝ f) x +
        (fderiv ℝ g x).smulRight (fderiv ℝ f x)) := by
  have he : fderiv ℝ (fun y => f y * g y) =
      fun y => f y • fderiv ℝ g y + g y • fderiv ℝ f y := by
    funext y
    exact fderiv_fun_mul (hf.differentiable (by simp) y) (hg.differentiable (by simp) y)
  rw [he]
  exact (((hf.differentiable (by simp) x).hasFDerivAt.smul
    (((hg.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x).hasFDerivAt)).add
    ((hg.differentiable (by simp) x).hasFDerivAt.smul
    (((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x).hasFDerivAt))).fderiv

def detectorBumpDerivativeBound : ℕ :=
  1 + 2 * detectorProfileDerivativeBound 1 + 2 * detectorProfileDerivativeBound 2 +
    2 * detectorProfileDerivativeBound 1 ^ 2

theorem coordinateProfile_derivative_bounds {b : ℝ}
    (hb : 0 < b) (hb₁ : b ≤ 1 / 16) (i : Fin 2) (x : EuclideanPlane) :
    ‖fderiv ℝ (fun y : EuclideanPlane => detectorProfile b (y i)) x‖ ≤
        b⁻¹ * (detectorProfileDerivativeBound 1 : ℝ) ∧
      ‖fderiv ℝ (fderiv ℝ (fun y : EuclideanPlane => detectorProfile b (y i))) x‖ ≤
        b⁻¹ ^ 2 * (detectorProfileDerivativeBound 2 : ℝ) := by
  have h₁ : |deriv (detectorProfile b) (x i)| ≤
      b⁻¹ * (detectorProfileDerivativeBound 1 : ℝ) := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero, pow_one] using
      detectorProfile_iteratedDeriv_bound hb hb₁ 1 (x i)
  have h₂ : |deriv (deriv (detectorProfile b)) (x i)| ≤
      b⁻¹ ^ 2 * (detectorProfileDerivativeBound 2 : ℝ) := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      detectorProfile_iteratedDeriv_bound hb hb₁ 2 (x i)
  constructor
  · rw [coordinateProfile_fderiv (detectorProfile_smooth hb), norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (euclideanCoordinate_norm i) (abs_nonneg _)).trans
      (by simpa only [mul_one] using h₁)
  · rw [coordinateProfile_second_fderiv (detectorProfile_smooth hb),
      ContinuousLinearMap.norm_smulRight_apply, norm_smul, Real.norm_eq_abs]
    calc
      _ ≤ |deriv (deriv (detectorProfile b)) (x i)| * 1 * 1 := by
        gcongr <;> exact euclideanCoordinate_norm i
      _ ≤ _ := by simpa only [mul_one] using h₂

theorem detectorBump_euclidean_derivative_bounds {b : ℝ}
    (hb : 0 < b) (hb₁ : b ≤ 1 / 16) (x : EuclideanPlane) :
    ‖fderiv ℝ (fun y : EuclideanPlane => detectorBump b (planeCoordinates y)) x‖ ≤
        (detectorBumpDerivativeBound : ℝ) * b⁻¹ ∧
      ‖fderiv ℝ (fderiv ℝ
        (fun y : EuclideanPlane => detectorBump b (planeCoordinates y))) x‖ ≤
        (detectorBumpDerivativeBound : ℝ) * b⁻¹ ^ 2 := by
  let f : EuclideanPlane → ℝ := fun y => detectorProfile b (y 0)
  let g : EuclideanPlane → ℝ := fun y => detectorProfile b (y 1)
  have hf : ContDiff ℝ ∞ f :=
    (detectorProfile_smooth hb).comp (euclideanCoordinate 0).contDiff
  have hg : ContDiff ℝ ∞ g :=
    (detectorProfile_smooth hb).comp (euclideanCoordinate 1).contDiff
  have hf₀ : ‖f x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (detectorProfile_range hb hb₁ (x 0)).1]
    exact (detectorProfile_range hb hb₁ (x 0)).2
  have hg₀ : ‖g x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (detectorProfile_range hb hb₁ (x 1)).1]
    exact (detectorProfile_range hb hb₁ (x 1)).2
  obtain ⟨hf₁, hf₂⟩ := coordinateProfile_derivative_bounds hb hb₁ 0 x
  obtain ⟨hg₁, hg₂⟩ := coordinateProfile_derivative_bounds hb hb₁ 1 x
  have hB₁ : (0 : ℝ) ≤ (detectorProfileDerivativeBound 1 : ℝ) := Nat.cast_nonneg _
  have hB₂ : (0 : ℝ) ≤ (detectorProfileDerivativeBound 2 : ℝ) := Nat.cast_nonneg _
  have hC₁ : 2 * (detectorProfileDerivativeBound 1 : ℝ) ≤
      (detectorBumpDerivativeBound : ℝ) := by
    unfold detectorBumpDerivativeBound
    push_cast
    nlinarith [hB₂,
      sq_nonneg (detectorProfileDerivativeBound 1 : ℝ)]
  have hC₂ : 2 * (detectorProfileDerivativeBound 2 : ℝ) +
      2 * (detectorProfileDerivativeBound 1 : ℝ) ^ 2 ≤
        (detectorBumpDerivativeBound : ℝ) := by
    unfold detectorBumpDerivativeBound
    push_cast
    linarith [hB₁]
  change ‖fderiv ℝ (fun y => f y * g y) x‖ ≤ _ ∧
    ‖fderiv ℝ (fderiv ℝ (fun y => f y * g y)) x‖ ≤ _
  constructor
  · rw [fderiv_fun_mul (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)]
    calc
      _ ≤ ‖f x • fderiv ℝ g x‖ + ‖g x • fderiv ℝ f x‖ := norm_add_le _ _
      _ = ‖f x‖ * ‖fderiv ℝ g x‖ + ‖g x‖ * ‖fderiv ℝ f x‖ := by
        rw [norm_smul, norm_smul]
      _ ≤ 1 * (b⁻¹ * (detectorProfileDerivativeBound 1 : ℝ)) +
          1 * (b⁻¹ * (detectorProfileDerivativeBound 1 : ℝ)) := by
        gcongr
      _ = (2 * (detectorProfileDerivativeBound 1 : ℝ)) * b⁻¹ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hC₁ (inv_nonneg.mpr hb.le)
  · rw [scalarProduct_second_fderiv hf hg]
    calc
      _ ≤ (‖f x‖ * ‖fderiv ℝ (fderiv ℝ g) x‖ +
          ‖fderiv ℝ f x‖ * ‖fderiv ℝ g x‖) +
          (‖g x‖ * ‖fderiv ℝ (fderiv ℝ f) x‖ +
          ‖fderiv ℝ g x‖ * ‖fderiv ℝ f x‖) := by
        have h := (norm_add_le
          (f x • fderiv ℝ (fderiv ℝ g) x +
            (fderiv ℝ f x).smulRight (fderiv ℝ g x))
          (g x • fderiv ℝ (fderiv ℝ f) x +
            (fderiv ℝ g x).smulRight (fderiv ℝ f x))).trans
          (add_le_add
            (norm_add_le (f x • fderiv ℝ (fderiv ℝ g) x)
              ((fderiv ℝ f x).smulRight (fderiv ℝ g x)))
            (norm_add_le (g x • fderiv ℝ (fderiv ℝ f) x)
              ((fderiv ℝ g x).smulRight (fderiv ℝ f x))))
        exact h.trans (add_le_add
          (add_le_add
            (ContinuousLinearMap.opNorm_smul_le (f x) (fderiv ℝ (fderiv ℝ g) x))
            (ContinuousLinearMap.norm_smulRight_apply _ _).le)
          (add_le_add
            (ContinuousLinearMap.opNorm_smul_le (g x) (fderiv ℝ (fderiv ℝ f) x))
            (ContinuousLinearMap.norm_smulRight_apply _ _).le))
      _ ≤ (1 * (b⁻¹ ^ 2 * (detectorProfileDerivativeBound 2 : ℝ)) +
          (b⁻¹ * (detectorProfileDerivativeBound 1 : ℝ)) ^ 2) +
          (1 * (b⁻¹ ^ 2 * (detectorProfileDerivativeBound 2 : ℝ)) +
          (b⁻¹ * (detectorProfileDerivativeBound 1 : ℝ)) ^ 2) := by
        simp only [pow_two]
        gcongr
        · simpa only [pow_two] using hg₂
        · simpa only [pow_two] using hf₂
      _ = (2 * (detectorProfileDerivativeBound 2 : ℝ) +
          2 * (detectorProfileDerivativeBound 1 : ℝ) ^ 2) * b⁻¹ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hC₂ (sq_nonneg _)

end ForcedComputation.VelocityDetector

end

end OAI
