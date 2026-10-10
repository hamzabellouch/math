import Mathlib

namespace OAI

universe uE

noncomputable section

open scoped RealInnerProductSpace

namespace Problem356.CoulombCalculus

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The real-valued radial Coulomb interaction, used only away from the origin. -/
def pairCost (x : E) : ℝ := ‖x‖⁻¹

/-- The gradient of the real radial Coulomb interaction. -/
def pairGradient (x : E) : E := -(‖x‖ ^ 3)⁻¹ • x

lemma hasFDerivAt_norm_explicit {x : E} (hx : x ≠ 0) :
    HasFDerivAt (fun y : E => ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt (pow_ne_zero 2 hn)
  simp only [Real.sqrt_sq (norm_nonneg x)] at h
  convert h using 1
  · ext y
    simp [Real.sqrt_sq (norm_nonneg y)]
  · ext y
    simp only [smul_apply, smul_eq_mul]
    field_simp
    simp [mul_comm]

lemma hasFDerivAt_pairCost {x : E} (hx : x ≠ 0) :
    HasFDerivAt (pairCost : E → ℝ) (-(‖x‖ ^ 3)⁻¹ • innerSL ℝ x) x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have h := (hasDerivAt_inv hn).comp_hasFDerivAt x (hasFDerivAt_norm_explicit hx)
  have hs : -(‖x‖ ^ 2)⁻¹ * ‖x‖⁻¹ = -(‖x‖ ^ 3)⁻¹ := by
    field_simp
  convert! h using 1
  simp only [smul_smul, hs]

lemma contDiffAt_pairCost {n : WithTop ENat} {x : E} (hx : x ≠ 0) :
    ContDiffAt ℝ n (pairCost : E → ℝ) x := by
  exact (contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)

/-- The Hessian of the real radial Coulomb interaction. -/
def pairHessian (x : E) : E →L[ℝ] E :=
  -(‖x‖ ^ 3)⁻¹ • ContinuousLinearMap.id ℝ E +
    (3 * (‖x‖ ^ 5)⁻¹) • (innerSL ℝ x).smulRight x

lemma hasFDerivAt_radialFactor {x : E} (hx : x ≠ 0) :
    HasFDerivAt (fun y : E => -(‖y‖ ^ 3)⁻¹)
      ((3 * (‖x‖ ^ 5)⁻¹) • innerSL ℝ x) x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have h := ((hasFDerivAt_pairCost hx).pow 3).neg
  convert! h using 1
  · ext y
    simp [pairCost, inv_pow]
  · ext y
    simp only [smul_apply, smul_eq_mul, neg_apply, pairCost]
    norm_num
    field_simp

lemma hasFDerivAt_pairGradient {x : E} (hx : x ≠ 0) :
    HasFDerivAt (pairGradient : E → E) (pairHessian x) x := by
  have h := (hasFDerivAt_radialFactor hx).smul (hasFDerivAt_id x)
  convert! h using 1
  ext y
  simp [pairHessian, ContinuousLinearMap.smulRight_apply, smul_smul]

lemma contDiffAt_pairGradient {n : WithTop ENat} {x : E} (hx : x ≠ 0) :
    ContDiffAt ℝ n (pairGradient : E → E) x := by
  exact (((contDiffAt_norm ℝ hx).pow 3).inv
    (pow_ne_zero 3 (norm_ne_zero_iff.mpr hx))).neg.smul contDiffAt_id

omit [InnerProductSpace ℝ E] in
@[simp] lemma pairCost_neg (x : E) : pairCost (-x) = pairCost x := by
  simp [pairCost]

@[simp] lemma pairGradient_neg (x : E) : pairGradient (-x) = -pairGradient x := by
  simp [pairGradient]

@[simp] lemma pairHessian_neg (x : E) : pairHessian (-x) = pairHessian x := by
  ext y
  simp [pairHessian]

lemma pairHessian_apply (x y : E) :
    pairHessian x y = -(‖x‖ ^ 3)⁻¹ • y +
      (3 * (‖x‖ ^ 5)⁻¹ * ⟪x, y⟫) • x := by
  simp [pairHessian, smul_smul]

lemma pairHessian_apply_self {x : E} (hx : x ≠ 0) :
    pairHessian x x = (2 * (‖x‖ ^ 3)⁻¹) • x := by
  rw [pairHessian_apply, real_inner_self_eq_norm_sq, ← add_smul]
  congr 1
  have hn := norm_ne_zero_iff.mpr hx
  field_simp
  ring

lemma pairHessian_apply_orthogonal {x y : E} (hxy : ⟪x, y⟫ = 0) :
    pairHessian x y = -(‖x‖ ^ 3)⁻¹ • y := by
  simp [pairHessian_apply, hxy]

lemma pairHessian_symmetric (x y z : E) :
    ⟪pairHessian x y, z⟫ = ⟪y, pairHessian x z⟫ := by
  simp only [pairHessian_apply, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm y x]
  ring

lemma pairHessian_smul_pos (x : E) {r : ℝ} (hr : 0 < r) :
    pairHessian (r • x) = (r ^ 3)⁻¹ • pairHessian x := by
  ext y
  simp only [pairHessian_apply, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
    real_inner_smul_left, smul_apply, smul_add, smul_smul]
  congr 1 <;> congr 1 <;> field_simp

lemma pairHessian_apply_of_norm_eq_one {x : E} (hx : ‖x‖ = 1) (y : E) :
    pairHessian x y = -y + (3 * ⟪x, y⟫) • x := by
  simp [pairHessian_apply, hx]

lemma pairHessian_injective {x : E} (hx : x ≠ 0) :
    Function.Injective (pairHessian x) := by
  apply (injective_iff_map_eq_zero (pairHessian x)).2
  intro y hy
  have hn : (‖x‖ ^ 3)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero 3 (norm_ne_zero_iff.mpr hx))
  have hxy : ⟪x, y⟫ = 0 := by
    have h := pairHessian_symmetric x x y
    rw [pairHessian_apply_self hx, hy, inner_zero_right, real_inner_smul_left] at h
    exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero (by norm_num) hn)
  rw [pairHessian_apply_orthogonal hxy] at hy
  exact (smul_eq_zero.mp hy).resolve_left (neg_ne_zero.mpr hn)

lemma pairHessian_isInvertible [FiniteDimensional ℝ E] {x : E} (hx : x ≠ 0) :
    (pairHessian x).IsInvertible := by
  have hi := pairHessian_injective hx
  have hs : Function.Surjective (pairHessian x).toLinearMap :=
    LinearMap.surjective_of_injective hi
  refine ⟨(LinearEquiv.ofBijective (pairHessian x).toLinearMap ⟨hi, hs⟩).toContinuousLinearEquiv, ?_⟩
  rfl

lemma fderiv_pairCost {x : E} (hx : x ≠ 0) :
    fderiv ℝ (pairCost : E → ℝ) x = innerSL ℝ (pairGradient x) := by
  rw [(hasFDerivAt_pairCost hx).fderiv]
  simp [pairGradient]

lemma hasFDerivAt_fderiv_pairCost {x : E} (hx : x ≠ 0) :
    HasFDerivAt (fderiv ℝ (pairCost : E → ℝ))
      ((innerSL ℝ).comp (pairHessian x)) x := by
  have h := (innerSL ℝ).hasFDerivAt.comp x (hasFDerivAt_pairGradient hx)
  apply h.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hx] with y hy
  exact fderiv_pairCost hy

lemma secondFDeriv_pairCost_apply {x : E} (hx : x ≠ 0) (v w : E) :
    fderiv ℝ (fderiv ℝ (pairCost : E → ℝ)) x v w = ⟪pairHessian x v, w⟫ := by
  rw [(hasFDerivAt_fderiv_pairCost hx).fderiv]
  rfl

lemma pairHessian_quadratic_lower (x y : E) :
    -(‖x‖ ^ 3)⁻¹ * ‖y‖ ^ 2 ≤ ⟪pairHessian x y, y⟫ := by
  rw [pairHessian_apply, inner_add_left, real_inner_smul_left,
    real_inner_smul_left, real_inner_self_eq_norm_sq]
  apply le_add_of_nonneg_right
  have hn : 0 ≤ 3 * (‖x‖ ^ 5)⁻¹ :=
    mul_nonneg (by norm_num) (inv_nonneg.mpr (pow_nonneg (norm_nonneg x) 5))
  nlinarith [mul_nonneg hn (sq_nonneg ⟪x, y⟫)]

end Problem356.CoulombCalculus

end

end OAI
