import OAI.Geometry.RCD.Coordinates.DifferentialStep
import OAI.Geometry.RCD.Coordinates.DifferentialBounds

namespace OAI

/-!
# Finite pointwise metric iteration

At a fixed point and direction, the map update supplies the metric
increment and the diagonal second-derivative recurrence. Field estimates,
inverse costs, cumulative budgets, and a leading comparison then control
the coordinate metric.
-/

open scoped BigOperators InnerProductSpace

noncomputable section

namespace RegularPointCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A common coefficient for the linear, inverse, squared, and recurrence errors. -/
def pointwiseIterationCoefficient (C : ℝ) : ℝ := C + 2 * C ^ 2 + 5 * C ^ 4

theorem pointwiseIterationCoefficient_bounds {C : ℝ} (hC : 1 ≤ C) :
    0 ≤ pointwiseIterationCoefficient C ∧ C ≤ pointwiseIterationCoefficient C ∧
      C ^ 2 ≤ pointwiseIterationCoefficient C ∧ 2 * C ^ 2 ≤ pointwiseIterationCoefficient C ∧
      5 * C ^ 4 ≤ pointwiseIterationCoefficient C := by
  have hC0 : 0 ≤ C := by linarith
  unfold pointwiseIterationCoefficient
  constructor
  · positivity
  constructor
  · nlinarith [sq_nonneg C, pow_nonneg hC0 4]
  constructor
  · nlinarith [sq_nonneg C, pow_nonneg hC0 4]
  constructor <;> nlinarith [sq_nonneg C, pow_nonneg hC0 4]

theorem sqrt_weighted_defect {energy q : ℝ} (henergy : 0 ≤ energy) (hq : 0 ≤ q) :
    Real.sqrt (energy * q ^ 2) = Real.sqrt energy * q := by
  rw [Real.sqrt_mul henergy, Real.sqrt_sq hq]

omit [CompleteSpace E] in
/-- The first derivative increment of the actual operator-field update. -/
theorem fderiv_clm_update_increment {h v : E → E} {K : E → E →L[ℝ] E} {x : E}
    (hh : DifferentiableAt ℝ h x) (hK : DifferentiableAt ℝ K x)
    (hv : DifferentiableAt ℝ v x) (xi : E) :
    fderiv ℝ (fun y => h y + K y (v y)) x xi - fderiv ℝ h x xi =
      K x (fderiv ℝ v x xi) + fderiv ℝ K x xi (v x) := by
  have hd := hh.hasFDerivAt.fun_add (hK.hasFDerivAt.clm_apply hv.hasFDerivAt)
  rw [hd.fderiv]
  simp

omit [CompleteSpace E] in
/-- The inverse linear error is measured by the normalized old diagonal
second derivative and the weighted defect. -/
theorem inverse_diagonal_error_le (K : E →L[ℝ] E) (dual : E → ℝ) (old v : E)
    {C epsilon r q energy : ℝ} (hC : 1 ≤ C)
    (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hr : 0 < r) (hq : 0 < q) (henergy : 0 ≤ energy)
    (hK : ∀ w, ‖K w‖ ≤ C * dual w)
    (hv : dual v ≤ C * Real.sqrt epsilon * r * Real.sqrt energy) :
    |⟪old, K v⟫_ℝ| ≤ C ^ 2 * (r / q * ‖old‖) * Real.sqrt (energy * q ^ 2) := by
  have hC0 : 0 ≤ C := by linarith
  have hsqrt : Real.sqrt epsilon ≤ 1 := by
    nlinarith [Real.sq_sqrt hepsilon, Real.sqrt_nonneg epsilon]
  have hvalue : ‖K v‖ ≤ C ^ 2 * r * Real.sqrt energy := by
    calc
      _ ≤ C * (C * Real.sqrt epsilon * r * Real.sqrt energy) :=
        (hK v).trans (mul_le_mul_of_nonneg_left hv hC0)
      _ = Real.sqrt epsilon * (C ^ 2 * r * Real.sqrt energy) := by ring
      _ ≤ _ := mul_le_of_le_one_left (by positivity) hsqrt
  calc
    _ ≤ ‖old‖ * ‖K v‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖old‖ * (C ^ 2 * r * Real.sqrt energy) :=
      mul_le_mul_of_nonneg_left hvalue (norm_nonneg _)
    _ = _ := by
      rw [sqrt_weighted_defect henergy hq.le]
      field_simp [ne_of_gt hq]

/-- The actual maps satisfy the finite metric comparison once their
explicit analytic estimates and geometric scalar budgets are supplied. -/
theorem pointwise_metric_iteration
    (h v : ℕ → E → E) (e : ℕ → E ≃L[ℝ] E)
    (principal : ℕ → E →L[ℝ] E) (dual : ℕ → E → ℝ)
    (x xi : E) (q r z energy : ℕ → ℝ) (k : ℕ)
    {C T epsilon Q : ℝ} (hC : 1 ≤ C) (hT : 1 ≤ T)
    (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1) (hQ : 0 ≤ Q)
    (hq : ∀ i, 0 < q i) (hr : ∀ i, 0 < r i)
    (hz : ∀ i, 0 ≤ z i) (henergy : ∀ i, 0 ≤ energy i)
    (hregular : ∀ i < k, ContDiffAt ℝ 3 (h i) x)
    (vregular : ∀ i < k, ContDiffAt ℝ 2 (v i) x)
    (hJacobian : ∀ i < k, fderiv ℝ (h i) x = (e i : E →L[ℝ] E))
    (hupdate : ∀ i < k, h (i + 1) = fun y => h i y +
      operatorInverseTranspose (fderiv ℝ (h i) y) (v i y))
    (hradius : ∀ i < k, r (i + 1) = r i / 2)
    (hmonotone : ∀ i < k, q i ≤ q (i + 1))
    (hinitial : diagonalSecond (h 0) x xi = 0)
    (hK : ∀ i < k, ∀ w,
      ‖operatorInverseTranspose (fderiv ℝ (h i) x) w‖ ≤ C * dual i w)
    (hK1 : ∀ i < k, ∀ w,
      ‖fderiv ℝ (fun y => operatorInverseTranspose (fderiv ℝ (h i) y)) x xi w‖ ≤
        C * q i / r i * dual i w)
    (hK2 : ∀ i < k, ∀ w,
      ‖diagonalSecond (fun y => operatorInverseTranspose (fderiv ℝ (h i) y)) x xi w‖ ≤
        C * (q i) ^ 2 / (r i) ^ 2 * dual i w)
    (hv : ∀ i < k, dual i (v i x) ≤
      C * Real.sqrt epsilon * r i * Real.sqrt (energy i))
    (hv1 : ∀ i < k, dual i (fderiv ℝ (v i) x xi) ≤
      C * Real.sqrt epsilon * (Real.sqrt (z i) + Real.sqrt (energy i) * q i))
    (hv2 : ∀ i < k, dual i (diagonalSecond (v i) x xi) ≤
      C / r i * (Real.sqrt (z i) * q i + Real.sqrt (energy i) * (q i) ^ 2))
    (hlinear : ∀ i < k, |⟪xi, fderiv ℝ (v i) x xi - principal i xi⟫_ℝ| ≤
      C * Real.sqrt (z i) * Real.sqrt (energy i) * q i)
    (hzbudget : (∑ i ∈ Finset.range k, z i) ≤ T * Q)
    (hdbudget : (∑ i ∈ Finset.range k, energy i * (q i) ^ 2) ≤ epsilon * Q)
    (hleadLower : T⁻¹ * Q ≤ ‖fderiv ℝ (h 0) x xi‖ ^ 2 +
      2 * ∑ i ∈ Finset.range k, ⟪xi, principal i xi⟫_ℝ)
    (hleadUpper : ‖fderiv ℝ (h 0) x xi‖ ^ 2 +
      2 * ∑ i ∈ Finset.range k, ⟪xi, principal i xi⟫_ℝ ≤ 2 * T * Q)
    (hsmall : scalarMetricErrorCoefficient (pointwiseIterationCoefficient C) T epsilon ≤
      (2 * T)⁻¹) :
    (4 * T)⁻¹ * Q ≤ ‖fderiv ℝ (h k) x xi‖ ^ 2 ∧
      ‖fderiv ℝ (h k) x xi‖ ^ 2 ≤ (4 * T) * Q := by
  let K : ℕ → E → E →L[ℝ] E := fun i y => operatorInverseTranspose (fderiv ℝ (h i) y)
  let m : ℕ → ℝ := fun i => ‖fderiv ℝ (h i) x xi‖ ^ 2
  let s : ℕ → ℝ := fun i => ⟪xi, principal i xi⟫_ℝ
  let d : ℕ → ℝ := fun i => energy i * (q i) ^ 2
  let b : ℕ → ℝ := fun i => r i / q i * ‖diagonalSecond (h i) x xi‖
  let linear : ℕ → ℝ := fun i => ⟪xi, fderiv ℝ (v i) x xi - principal i xi⟫_ℝ
  let inverse : ℕ → ℝ := fun i => -⟪diagonalSecond (h i) x xi, K i x (v i x)⟫_ℝ
  let square : ℕ → ℝ := fun i => ‖fderiv ℝ (h (i + 1)) x xi - fderiv ℝ (h i) x xi‖ ^ 2
  obtain ⟨hcoef, hcoef1, hcoef2, hcoefRec, hcoefSq⟩ := pointwiseIterationCoefficient_bounds hC
  have hKregular (i : ℕ) (hi : i < k) : ContDiffAt ℝ 2 (K i) x := by
    apply contDiffAt_inverseTranspose_field ((hregular i hi).fderiv_right (m := 2) (by norm_num))
    rw [hJacobian i hi]
    exact (e i).toUnit.isUnit
  have hdelta (i : ℕ) (hi : i < k) :
      fderiv ℝ (h (i + 1)) x xi - fderiv ℝ (h i) x xi =
        K i x (fderiv ℝ (v i) x xi) + fderiv ℝ (K i) x xi (v i x) := by
    rw [hupdate i hi]
    exact fderiv_clm_update_increment ((hregular i hi).differentiableAt (by norm_num))
      ((hKregular i hi).differentiableAt (by norm_num))
      ((vregular i hi).differentiableAt (by norm_num)) xi
  have hsecond (i : ℕ) (hi : i < k) : diagonalSecond (h (i + 1)) x xi =
      diagonalSecond (h i) x xi + (K i x (diagonalSecond (v i) x xi) +
        (2 : ℝ) • fderiv ℝ (K i) x xi (fderiv ℝ (v i) x xi) +
        diagonalSecond (K i) x xi (v i x)) := by
    rw [hupdate i hi, diagonalSecond_add ((hregular i hi).of_le (by norm_num))
      ((hKregular i hi).clm_apply (vregular i hi)),
      diagonalSecond_clm_apply (hKregular i hi) (vregular i hi)]
    simp only [two_smul]
  have hd : ∀ i, 0 ≤ d i := fun i => mul_nonneg (henergy i) (sq_nonneg _)
  have hb : ∀ i, 0 ≤ b i := by
    intro i
    exact mul_nonneg (div_nonneg (hr i).le (hq i).le) (norm_nonneg _)
  have hbzero : b 0 = 0 := by simp [b, hinitial]
  have hrec : ∀ i < k, b (i + 1) ≤ b i / 2 +
      pointwiseIterationCoefficient C * (Real.sqrt (z i) + Real.sqrt (d i)) := by
    intro i hi
    have hqi := hq i
    have hbound := differential_diagonal_update_recurrence
      (K i x) (fderiv ℝ (K i) x xi) (diagonalSecond (K i) x xi) (dual i)
      (v i x) (fderiv ℝ (v i) x xi) (diagonalSecond (v i) x xi)
      (diagonalSecond (h i) x xi) (diagonalSecond (h (i + 1)) x xi)
      hC hepsilon hepsilon1 (hq i) (hr i) (hmonotone i hi)
      (hK i hi) (hK1 i hi) (hK2 i hi) (hv i hi) (hv1 i hi) (hv2 i hi) (hsecond i hi)
    have hroot : Real.sqrt (d i) = Real.sqrt (energy i) * q i :=
      sqrt_weighted_defect (henergy i) (hq i).le
    dsimp [b]
    rw [hradius i hi, hroot]
    exact hbound.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_right hcoefRec (by positivity)))
  have hlin : ∀ i < k, |linear i| ≤ pointwiseIterationCoefficient C *
      Real.sqrt (z i) * Real.sqrt (d i) := by
    intro i hi
    have hqi := hq i
    dsimp [linear, d]
    rw [sqrt_weighted_defect (henergy i) (hq i).le]
    calc
      _ ≤ C * Real.sqrt (z i) * Real.sqrt (energy i) * q i := hlinear i hi
      _ = C * (Real.sqrt (z i) * (Real.sqrt (energy i) * q i)) := by ring
      _ ≤ pointwiseIterationCoefficient C * (Real.sqrt (z i) * (Real.sqrt (energy i) * q i)) :=
        mul_le_mul_of_nonneg_right hcoef1 (by positivity)
      _ = _ := by ring
  have hinv : ∀ i < k, |inverse i| ≤ pointwiseIterationCoefficient C * b i * Real.sqrt (d i) := by
    intro i hi
    have hqi := hq i
    have hri := hr i
    dsimp [inverse]
    rw [abs_neg]
    have hbound := inverse_diagonal_error_le (K i x) (dual i) (diagonalSecond (h i) x xi)
      (v i x) hC hepsilon hepsilon1 (hr i) (hq i) (henergy i) (hK i hi) (hv i hi)
    exact hbound.trans (by
      dsimp [b, d]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoef2 (by positivity)) (Real.sqrt_nonneg _))
  have hsquare : ∀ i < k, |square i| ≤ pointwiseIterationCoefficient C * epsilon * (z i + d i) := by
    intro i hi
    have hzi := hz i
    have hEi := henergy i
    dsimp [square]
    rw [abs_of_nonneg (sq_nonneg _), hdelta i hi]
    have hbound := differential_first_increment_sq_le (K i x) (fderiv ℝ (K i) x xi)
      (dual i) (v i x) (fderiv ℝ (v i) x xi) hC hepsilon (hq i) (hr i)
      (hz i) (henergy i) (hK i hi) (hK1 i hi) (hv i hi) (hv1 i hi)
    exact hbound.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoefSq hepsilon) (by positivity))
  have hmetricStep : ∀ i < k, m (i + 1) - m i =
      2 * s i + 2 * linear i + 2 * inverse i + square i := by
    intro i hi
    have hidentity := inverseTranspose_update_metric_increment
      ((hregular i hi).of_le (by norm_num))
      ((vregular i hi).differentiableAt (by norm_num)) (e i) (hJacobian i hi) xi
    dsimp only at hidentity
    rw [← hupdate i hi] at hidentity
    have hKvalue : K i x = inverseTranspose (e i) := by
      dsimp [K]
      rw [hJacobian i hi, operatorInverseTranspose_equiv]
    have hJxi : (e i) xi = fderiv ℝ (h i) x xi := by
      rw [hJacobian i hi]
      rfl
    rw [← hKvalue, hJxi] at hidentity
    dsimp [m, s, linear, inverse, square]
    rw [inner_sub_right]
    nlinarith [hidentity]
  exact scalar_metric_bootstrap hcoef hT hepsilon hQ hz hd hb hbzero k
    hrec hlin hinv hsquare hmetricStep hzbudget hdbudget hleadLower hleadUpper hsmall

end RegularPointCoordinates

end

end OAI
