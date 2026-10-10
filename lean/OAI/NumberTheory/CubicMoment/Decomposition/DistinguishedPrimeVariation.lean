import OAI.NumberTheory.CubicMoment.Estimates.LongPrimeWeights

namespace OAI

/-! Actual radial weights when the largest prime lies in a distinguished
tuple coordinate. The detector difference has a uniform scaled derivative,
so the original smooth weight, rather than an arbitrary bounded sequence,
can be used in prime partial summation. -/
noncomputable section
open scoped ContDiff
namespace CubicFirstMoment

def distinguishedRadialWeight (W : ℝ → ℂ) (w z x : ℝ) : ℂ :=
  W x*((primeDetectorCutoff (x/w):ℂ)-(primeDetectorCutoff (x/z):ℂ))

lemma detector_difference_smooth (w z : ℝ) :
    ContDiff ℝ ∞ (fun x : ℝ =>
      (primeDetectorCutoff (x/w):ℂ)-(primeDetectorCutoff (x/z):ℂ)) :=
  (primeDetectorCutoff_rescaled_smooth w).sub (primeDetectorCutoff_rescaled_smooth z)

lemma detector_difference_norm (w z x : ℝ) :
    ‖(primeDetectorCutoff (x/w):ℂ)-(primeDetectorCutoff (x/z):ℂ)‖ ≤ 1 := by
  rw [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  apply abs_le.mpr
  constructor <;> linarith [primeDetectorCutoff_nonneg (x/w),primeDetectorCutoff_le_one (x/w),
    primeDetectorCutoff_nonneg (x/z),primeDetectorCutoff_le_one (x/z)]

lemma detector_difference_deriv {E : ℝ}
    (hE : ∀ x : ℝ, 0 < x → |deriv primeDetectorCutoff x| * x ≤ E)
    {w z x : ℝ} (hw : 0 < w) (hz : 0 < z) (hx : 0 < x) :
    ‖deriv (fun t : ℝ => (primeDetectorCutoff (t/w):ℂ)-
      (primeDetectorCutoff (t/z):ℂ)) x‖*x ≤ 2*E := by
  have hdw := ((primeDetectorCutoff_rescaled_smooth w).differentiable
    (by norm_num)).differentiableAt (x := x)
  have hdz := ((primeDetectorCutoff_rescaled_smooth z).differentiable
    (by norm_num)).differentiableAt (x := x)
  have he : deriv (fun t : ℝ => (primeDetectorCutoff (t/w):ℂ)-
      (primeDetectorCutoff (t/z):ℂ)) x =
      deriv (fun t : ℝ => (primeDetectorCutoff (t/w):ℂ)) x-
        deriv (fun t : ℝ => (primeDetectorCutoff (t/z):ℂ)) x := by
    exact deriv_fun_sub hdw hdz
  rw [he]
  calc
    _ ≤ (‖deriv (fun t : ℝ => (primeDetectorCutoff (t/w):ℂ)) x‖+
        ‖deriv (fun t : ℝ => (primeDetectorCutoff (t/z):ℂ)) x‖)*x :=
      mul_le_mul_of_nonneg_right (norm_sub_le _ _) hx.le
    _ = ‖deriv (fun t : ℝ => (primeDetectorCutoff (t/w):ℂ)) x‖*x+
        ‖deriv (fun t : ℝ => (primeDetectorCutoff (t/z):ℂ)) x‖*x := by ring
    _ ≤ E+E := add_le_add (primeDetectorCutoff_rescaled_deriv hE hw hx)
      (primeDetectorCutoff_rescaled_deriv hE hz hx)
    _ = _ := by ring

theorem distinguishedRadialWeight_bounds (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W)
    {M D E w z : ℝ} (hM : 0 ≤ M) (hD : 0 ≤ D) (_hE : 0 ≤ E)
    (hw : 0 < w) (hz : 0 < z) (hWnorm : ∀ x, ‖W x‖ ≤ M)
    (hWderiv : ∀ x, 0 < x → ‖deriv W x‖*x ≤ D)
    (hdet : ∀ x : ℝ, 0 < x → |deriv primeDetectorCutoff x| * x ≤ E) :
    ContDiff ℝ ∞ (distinguishedRadialWeight W w z) ∧
    (∀ x, ‖distinguishedRadialWeight W w z x‖ ≤ M) ∧
    (∀ x, 0 < x → ‖deriv (distinguishedRadialWeight W w z) x‖*x ≤ D+2*E*M) := by
  let φ := fun x : ℝ => (primeDetectorCutoff (x/w):ℂ)-(primeDetectorCutoff (x/z):ℂ)
  have hφ := detector_difference_smooth w z
  refine ⟨hW.mul hφ,?_,?_⟩
  · intro x
    change ‖W x*((primeDetectorCutoff (x/w):ℂ)-(primeDetectorCutoff (x/z):ℂ))‖ ≤ M
    rw [norm_mul]
    exact (mul_le_mul (hWnorm x) (detector_difference_norm w z x)
      (_root_.norm_nonneg _) hM).trans_eq (mul_one M)
  · intro x hx
    have hdW := (hW.differentiable (by norm_num)).differentiableAt (x := x)
    have hdφ := (hφ.differentiable (by norm_num)).differentiableAt (x := x)
    change ‖deriv (fun x => W x*φ x) x‖*x ≤ _
    have he : deriv (fun t => W t*φ t) x = deriv W x*φ x+W x*deriv φ x := by
      exact deriv_fun_mul hdW hdφ
    rw [he]
    calc
      _ ≤ (‖deriv W x*φ x‖+‖W x*deriv φ x‖)*x :=
        mul_le_mul_of_nonneg_right (norm_add_le _ _) hx.le
      _ = (‖deriv W x‖*x)*‖φ x‖+‖W x‖*(‖deriv φ x‖*x) := by
        rw [norm_mul,norm_mul]
        ring
      _ ≤ D*1+M*(2*E) := add_le_add
        (mul_le_mul (hWderiv x hx) (detector_difference_norm w z x)
          (_root_.norm_nonneg _) hD)
        (mul_le_mul (hWnorm x) (detector_difference_deriv hdet hw hz hx)
          (mul_nonneg (_root_.norm_nonneg _) hx.le) hM)
      _ = _ := by ring

end CubicFirstMoment

end

end OAI
