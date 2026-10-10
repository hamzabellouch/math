import OAI.Analysis.FiniteFactor.BoundedMatrixOperator

namespace OAI

namespace FiniteFactor
open Filter
open scoped ENNReal
noncomputable section

/-- Coordinate translation on the original l2 fiber. -/
def fiberShiftVector (n : ℤ) (v : SourceFiberHilbert) : SourceFiberHilbert :=
  ⟨fun k => v (k-n), memℓp_gen
    ((Equiv.subRight n).summable_iff.mpr ((lp.memℓp v).summable (by norm_num)))⟩

theorem fiberShiftVector_norm (n : ℤ) (v : SourceFiberHilbert) :
    ‖fiberShiftVector n v‖ = ‖v‖ := by
  have he : ‖fiberShiftVector n v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [show ‖fiberShiftVector n v‖ ^ 2 =
      ∑' k, ‖fiberShiftVector n v k‖ ^ 2 by
        simpa using lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (fiberShiftVector n v)]
    rw [show ‖v‖ ^ 2 = ∑' k, ‖v k‖ ^ 2 by
      simpa using lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) v]
    exact (Equiv.subRight n).tsum_eq (fun k => ‖v k‖ ^ 2)
  nlinarith [norm_nonneg (fiberShiftVector n v), norm_nonneg v]

def fiberShift (n : ℤ) : SourceFiberHilbert →L[ℂ] SourceFiberHilbert :=
  LinearMap.mkContinuous
    { toFun := fiberShiftVector n
      map_add' := fun u v => rfl
      map_smul' := fun c v => rfl }
    1 (fun v => by
      change ‖fiberShiftVector n v‖ ≤ 1 * ‖v‖
      rw [one_mul, fiberShiftVector_norm])

@[simp] theorem fiberShift_apply (n : ℤ) (v : SourceFiberHilbert) (k : ℤ) :
    fiberShift n v k = v (k-n) := rfl

theorem fiberShift_single (n m : ℤ) (c : ℂ) :
    fiberShift n (lp.single 2 m c) = lp.single 2 (m+n) c := by
  classical
  apply Subtype.ext
  funext k
  change (lp.single 2 m c : SourceFiberHilbert) (k-n) =
    (lp.single 2 (m+n) c : SourceFiberHilbert) k
  by_cases h : m = k-n
  · simp [lp.single_apply, h]
  · have hh : m+n ≠ k := by omega
    simp [lp.single_apply, h, hh]

@[simp] theorem fiberShift_mul (n m : ℤ) : fiberShift n * fiberShift m = fiberShift (n+m) := by
  apply ContinuousLinearMap.ext
  intro v
  apply Subtype.ext
  funext k
  change v (k-n-m) = v (k-(n+m))
  exact congrArg v (by omega)

@[simp] theorem fiberShift_zero : fiberShift 0 = 1 := by
  apply ContinuousLinearMap.ext
  intro v
  apply Subtype.ext
  funext k
  change v (k-0) = v k
  rw [sub_zero]

theorem fiber_covariance_operator
    (A B : SourceFiberHilbert →L[ℂ] SourceFiberHilbert) (n : ℤ)
    (h : ∀ k m : ℤ, (B (lp.single 2 m (1 : ℂ))) k =
      (A (lp.single 2 (m+n) (1 : ℂ))) (k+n)) :
    fiberShift (-n) * A = B * fiberShift (-n) := by
  apply fiberOperator_ext
  intro k m
  change (A (lp.single 2 m (1 : ℂ))) (k-(-n)) =
    (B (fiberShift (-n) (lp.single 2 m (1 : ℂ)))) k
  rw [fiberShift_single, h]
  simp

/-- Invariance of a projection range persists under every nonnegative power. -/
theorem invariant_projection_pow {R : Type*} [Ring R] (p T : R)
    (hp : p*p = p) (hinv : (1-p)*T*p = 0) : ∀ n : ℕ, (1-p)*(T^n)*p = 0 := by
  have hTp : T*p = p*T*p := by
    have h := hinv
    rw [sub_mul, one_mul, sub_mul] at h
    exact sub_eq_zero.mp h
  have hfix : ∀ n : ℕ, T^n*p = p*(T^n)*p := by
    intro n
    induction n with
    | zero => simpa using hp.symm
    | succ n ih =>
      calc
        T^(n+1)*p = T*(T^n*p) := by rw [pow_succ', mul_assoc]
        _ = T*(p*T^n*p) := by rw [ih]
        _ = (T*p)*T^n*p := by simp only [mul_assoc]
        _ = (p*T*p)*T^n*p := by rw [hTp]
        _ = p*T*(p*T^n*p) := by simp only [mul_assoc]
        _ = p*T*(T^n*p) := by rw [← ih]
        _ = p*T^(n+1)*p := by rw [pow_succ']; simp only [mul_assoc]
  intro n
  rw [sub_mul, one_mul, sub_mul, hfix n]
  simp only [mul_assoc, sub_self]

end
end FiniteFactor

end OAI
