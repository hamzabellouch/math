import OAI.Geometry.CylinderCovering.Rational.FieldDefinitions
import OAI.Geometry.CylinderCovering.Rational.Domain

namespace OAI

noncomputable section
open scoped ContDiff

namespace SlopeRational

@[simp] theorem vec2_zero (x y : ℝ) : vec2 x y 0 = x := rfl
@[simp] theorem vec2_one (x y : ℝ) : vec2 x y 1 = y := rfl

theorem a_even (d Y T : ℝ) : a d (-Y) T = a d Y T := by
  simp [a]

theorem b_odd (d Y T : ℝ) : b d (-Y) T = -b d Y T := by
  unfold b
  ring

theorem a_simplified (d Y T : ℝ) (h : radius T + d ≠ 0) :
    a d Y T = -1 / 16 + (d ^ 2 - 4 * Y ^ 2) / (16 * (radius T + d) ^ 2) := by
  unfold a
  field_simp
  ring

theorem ceilingCoefficient_eq (d Y : ℝ) : ceilingCoefficient d Y = -a d Y 0 := by
  simp only [ceilingCoefficient, ceilingConstant, ceilingQuadratic, a, radius, sub_zero]
  ring

theorem b_at_divider (d Y : ℝ) : b d Y 0 = alpha d * Y := by
  unfold b alpha radius
  ring

theorem ceiling_square_surplus (d x y : ℝ) :
    ceilingPolynomial d x + ceilingPolynomial d y -
      alpha d * (x ^ 2 * ceilingCoefficient d y + y ^ 2 * ceilingCoefficient d x) =
      alpha d * ceilingQuadratic d * (x ^ 2 - y ^ 2) ^ 2 := by
  unfold ceilingPolynomial ceilingCoefficient
  ring

theorem ceiling_square_surplus_nonneg (d x y : ℝ) (hd : 0 < d) :
    0 ≤ ceilingPolynomial d x + ceilingPolynomial d y -
      alpha d * (x ^ 2 * ceilingCoefficient d y + y ^ 2 * ceilingCoefficient d x) := by
  rw [ceiling_square_surplus]
  unfold alpha ceilingQuadratic
  positivity

theorem right_wall_tangent (d T : ℝ) (h : radius T + d ≠ 0) :
    a d (radius T / 2) T + b d (radius T / 2) T / 2 = 0 := by
  unfold a b
  field_simp
  ring

theorem left_wall_tangent (d T : ℝ) (h : radius T + d ≠ 0) :
    a d (-radius T / 2) T - b d (-radius T / 2) T / 2 = 0 := by
  unfold a b
  field_simp
  ring

theorem potential_right_wall (d T : ℝ) : potential d (radius T / 2) T = 0 := by
  unfold potential
  have : (radius T / 2) ^ 2 - radius T ^ 2 / 4 = 0 := by ring
  rw [this, zero_div]

theorem potential_left_wall (d T : ℝ) : potential d (-radius T / 2) T = 0 := by
  unfold potential
  have : (-radius T / 2) ^ 2 - radius T ^ 2 / 4 = 0 := by ring
  rw [this, zero_div]

def matrixCLM (a b c d : ℝ) : Plane →L[ℝ] Plane :=
  (a • EuclideanSpace.proj 0 + b • EuclideanSpace.proj 1 : Plane →L[ℝ] ℝ).smulRight
      (vec2 1 0) +
    (c • EuclideanSpace.proj 0 + d • EuclideanSpace.proj 1 : Plane →L[ℝ] ℝ).smulRight
      (vec2 0 1)

@[simp] theorem matrixCLM_apply (a b c d : ℝ) (z : Plane) :
    matrixCLM a b c d z = vec2 (a * z 0 + b * z 1) (c * z 0 + d * z 1) := by
  ext i
  fin_cases i <;> simp [matrixCLM, vec2]

theorem hasFDerivAt_vec2 {f g : Plane → ℝ} {f' g' : Plane →L[ℝ] ℝ} {z : Plane}
    (hf : HasFDerivAt f f' z) (hg : HasFDerivAt g g' z) :
    HasFDerivAt (fun w => vec2 (f w) (g w))
      (f'.smulRight (vec2 1 0) + g'.smulRight (vec2 0 1)) z := by
  have he : (fun w => vec2 (f w) (g w)) =
      (fun w => f w • vec2 1 0 + g w • vec2 0 1) := by
    funext w
    ext i
    fin_cases i <;> simp [vec2]
  rw [he]
  exact (hf.smul_const (vec2 1 0)).add (hg.smul_const (vec2 0 1))

theorem field_fderiv (d : ℝ) {z : Plane} (h : radius (z 1) + d ≠ 0) :
    fderiv ℝ (field d) z =
      matrixCLM (-z 0 / (2 * (radius (z 1) + d) ^ 2))
        ((d ^ 2 - 4 * z 0 ^ 2) / (8 * (radius (z 1) + d) ^ 3))
        (1 / (2 * (radius (z 1) + d)))
        (z 0 / (2 * (radius (z 1) + d) ^ 2)) := by
  let y : Plane →L[ℝ] ℝ := EuclideanSpace.proj 0
  let t : Plane →L[ℝ] ℝ := EuclideanSpace.proj 1
  have hy := y.hasFDerivAt (x := z)
  have ht := t.hasFDerivAt (x := z)
  have hr := ht.const_sub (1 / 2 : ℝ)
  have hd := hr.add_const d
  have h4 : 4 * (1 / 2 - t z + d) ^ 2 ≠ 0 := by
    change 4 * (radius (z 1) + d) ^ 2 ≠ 0
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ h)
  have h16 : 16 * (1 / 2 - t z + d) ^ 2 ≠ 0 := by
    change 16 * (radius (z 1) + d) ^ 2 ≠ 0
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ h)
  have h2 : 2 * (1 / 2 - t z + d) ≠ 0 := by
    change 2 * (radius (z 1) + d) ≠ 0
    exact mul_ne_zero (by norm_num) h
  have hi4 := (hasDerivAt_inv h4).comp_hasFDerivAt z ((hd.pow 2).const_mul 4)
  have hi16 := (hasDerivAt_inv h16).comp_hasFDerivAt z ((hd.pow 2).const_mul 16)
  have hi2 := (hasDerivAt_inv h2).comp_hasFDerivAt z (hd.const_mul 2)
  have hA := ((hy.pow 2).neg.mul hi4).sub ((hr.mul (hr.add_const (2 * d))).mul hi16)
  have hB := hy.mul hi2
  have hf := (hasFDerivAt_vec2 hA hB).fderiv
  change fderiv ℝ (field d) z = _ at hf
  rw [hf]
  ext w i
  fin_cases i <;>
    simp [matrixCLM, y, t, ContinuousLinearMap.smulRight_apply, vec2, radius] <;>
    field_simp [show 1 / 2 - z 1 + d ≠ 0 from h] <;> ring

theorem matrixCLM_trace (a b c d : ℝ) :
    LinearMap.trace ℝ Plane (matrixCLM a b c d).toLinearMap = a + d := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis,
    Matrix.trace_fin_two]
  simp [LinearMap.toMatrix_apply, EuclideanSpace.basisFun_apply,
    EuclideanSpace.basisFun_repr, matrixCLM_apply]

theorem matrixCLM_det (a b c d : ℝ) :
    LinearMap.det (matrixCLM a b c d).toLinearMap = a * d - b * c := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis,
    Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, EuclideanSpace.basisFun_apply,
    EuclideanSpace.basisFun_repr, matrixCLM_apply]

theorem field_trace_det (d : ℝ) {z : Plane} (h : radius (z 1) + d ≠ 0) :
    LinearMap.trace ℝ Plane (fderiv ℝ (field d) z).toLinearMap = 0 ∧
      LinearMap.det (fderiv ℝ (field d) z).toLinearMap =
        -d ^ 2 / (16 * (radius (z 1) + d) ^ 4) := by
  rw [field_fderiv d h, matrixCLM_trace, matrixCLM_det]
  constructor
  · ring
  · field_simp
    ring

theorem field_det_neg (d : ℝ) (hd : 0 < d) {z : Plane}
    (h : radius (z 1) + d ≠ 0) :
    LinearMap.det (fderiv ℝ (field d) z).toLinearMap < 0 := by
  rw [(field_trace_det d h).2]
  apply div_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_pos hd))
  have hp : 0 < ((radius (z 1) + d) ^ 2) ^ 2 := pow_pos (sq_pos_of_ne_zero h) 2
  nlinarith

theorem field_contDiffAt (d : ℝ) {z : Plane} (h : radius (z 1) + d ≠ 0) :
    ContDiffAt ℝ ∞ (field d) z := by
  apply contDiffAt_euclidean.mpr
  intro i
  fin_cases i
  · change ContDiffAt ℝ ∞ (fun w : Plane => a d (w 0) (w 1)) z
    unfold a radius
    apply ContDiffAt.sub
    · apply ContDiffAt.div (by fun_prop) (by fun_prop)
      exact mul_ne_zero (by norm_num) (pow_ne_zero _ h)
    · apply ContDiffAt.div (by fun_prop) (by fun_prop)
      exact mul_ne_zero (by norm_num) (pow_ne_zero _ h)
  · change ContDiffAt ℝ ∞ (fun w : Plane => b d (w 0) (w 1)) z
    unfold b radius
    apply ContDiffAt.div (by fun_prop) (by fun_prop)
    exact mul_ne_zero (by norm_num) h

theorem field_contDiffOn (d : ℝ) :
    ContDiffOn ℝ ∞ (field d) {z : Plane | radius (z 1) + d ≠ 0} :=
  fun _ hz => (field_contDiffAt d hz).contDiffWithinAt

theorem radius_nonneg_of_mem_wedge {z : Plane} (hz : z ∈ wedge) : 0 ≤ radius (z 1) := by
  exact le_trans (mul_nonneg (by norm_num) (abs_nonneg _)) hz

theorem denominator_pos_of_mem_wedge {d : ℝ} (hd : 0 < d) {z : Plane} (hz : z ∈ wedge) :
    0 < radius (z 1) + d := add_pos_of_nonneg_of_pos (radius_nonneg_of_mem_wedge hz) hd

theorem field_smoothNear_labelDomain {d : ℝ} (hd : 0 < d) (ε q : ℝ) :
    ∃ U : Set Plane, IsOpen U ∧ labelDomain d ε q ⊆ U ∧ ContDiffOn ℝ ∞ (field d) U := by
  refine ⟨{z : Plane | radius (z 1) + d ≠ 0}, ?_, ?_, field_contDiffOn d⟩
  · exact isOpen_ne_fun (by unfold radius; fun_prop) continuous_const
  · intro z hz
    exact (denominator_pos_of_mem_wedge hd hz.1).ne'

theorem plane_charpoly (A : Plane →ₗ[ℝ] Plane) :
    A.charpoly = Polynomial.X ^ 2 -
      Polynomial.C (LinearMap.trace ℝ Plane A) * Polynomial.X + Polynomial.C (LinearMap.det A) := by
  rw [← LinearMap.charpoly_toMatrix A (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis,
    Matrix.charpoly_fin_two, LinearMap.det_toMatrix, ← LinearMap.trace_eq_matrix_trace]

theorem field_eigenvalues (d : ℝ) {z : Plane} (h : radius (z 1) + d ≠ 0) :
    Module.End.HasEigenvalue (fderiv ℝ (field d) z).toLinearMap
        (d / (4 * (radius (z 1) + d) ^ 2)) ∧
      Module.End.HasEigenvalue (fderiv ℝ (field d) z).toLinearMap
        (-(d / (4 * (radius (z 1) + d) ^ 2))) := by
  have ht := (field_trace_det d h).1
  have hd := (field_trace_det d h).2
  constructor <;>
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Polynomial.IsRoot, plane_charpoly, ht, hd] <;>
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_mul, Polynomial.eval_C, zero_mul, sub_zero] <;>
    field_simp <;> ring

theorem labelDomain_coordinate_bounds (d ε q : ℝ) {z : Plane} (hz : z ∈ labelDomain d ε q) :
    |z 0| ≤ 3 / 8 ∧ -(1 / 4 : ℝ) ≤ z 1 ∧ z 1 ≤ 1 / 2 := by
  have hw := hz.1
  change 2 * |z 0| ≤ 1 / 2 - z 1 at hw
  have ht := hz.2.1
  refine ⟨by linarith, ht, ?_⟩
  linarith [abs_nonneg (z 0)]

theorem plane_norm_sq (z : Plane) : ‖z‖ ^ 2 = z 0 ^ 2 + z 1 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg ‖z i‖))]
  simp [Fin.sum_univ_succ, Real.norm_eq_abs]

theorem plane_norm_le_sum (z : Plane) : ‖z‖ ≤ |z 0| + |z 1| := by
  have h := plane_norm_sq z
  have h0 := abs_nonneg (z 0)
  have h1 := abs_nonneg (z 1)
  nlinarith [sq_abs (z 0), sq_abs (z 1)]

theorem eigenvalue_smul (A : Plane →ₗ[ℝ] Plane) {lam : ℝ}
    (hlam : Module.End.HasEigenvalue A lam) (k : ℝ) :
    Module.End.HasEigenvalue (k • A) (k * lam) := by
  obtain ⟨u, hu⟩ := hlam.exists_hasEigenvector
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := u)
  constructor
  · rw [Module.End.mem_eigenspace_iff]
    change k • A u = (k * lam) • u
    rw [hu.apply_eq_smul, mul_smul]
  · exact hu.2

theorem scaled_field_eigenvalues (d ε : ℝ) {z : Plane} (h : radius (z 1) + d ≠ 0) :
    Module.End.HasEigenvalue (fderiv ℝ (fun w => ε • field d w) z).toLinearMap
        (ε * d / (4 * (radius (z 1) + d) ^ 2)) ∧
      Module.End.HasEigenvalue (fderiv ℝ (fun w => ε • field d w) z).toLinearMap
        (-(ε * d / (4 * (radius (z 1) + d) ^ 2))) := by
  rw [fderiv_fun_const_smul ((field_contDiffAt d h).differentiableAt (by norm_num))]
  obtain ⟨hp, hm⟩ := field_eigenvalues d h
  constructor
  · simpa [mul_div_assoc] using eigenvalue_smul _ hp ε
  · simpa [mul_div_assoc] using eigenvalue_smul _ hm ε

theorem eigenvalue_bound_on_wedge {d : ℝ} (hd : 0 < d) {z : Plane} (hz : z ∈ wedge) :
    0 < d / (4 * (radius (z 1) + d) ^ 2) ∧
      d / (4 * (radius (z 1) + d) ^ 2) ≤ 1 / (4 * d) := by
  have hr := radius_nonneg_of_mem_wedge hz
  have hden := denominator_pos_of_mem_wedge hd hz
  constructor
  · exact div_pos hd (mul_pos (by norm_num) (sq_pos_of_pos hden))
  · apply (div_le_div_iff₀ (mul_pos (by norm_num) (sq_pos_of_pos hden))
      (mul_pos (by norm_num) hd)).mpr
    nlinarith [sq_nonneg (radius (z 1)), mul_nonneg hr hd.le]

theorem scaled_field_spectral_window {d L ε : ℝ} (hd : 0 < d) (hL : 0 < L)
    (hε : 0 < ε) (hsmall : L * ε < 4 * d) {z : Plane} (hz : z ∈ wedge) :
    0 < L * (ε * d / (4 * (radius (z 1) + d) ^ 2)) ∧
      L * (ε * d / (4 * (radius (z 1) + d) ^ 2)) < 1 := by
  obtain ⟨hpos, hbound⟩ := eigenvalue_bound_on_wedge hd hz
  have hLe : 0 < L * ε := mul_pos hL hε
  have hbound' := mul_le_mul_of_nonneg_left hbound hLe.le
  have hsmall' : L * ε * (1 / (4 * d)) < 1 := by
    rw [mul_one_div, div_lt_one (mul_pos (by norm_num) hd)]
    exact hsmall
  constructor
  · simpa [mul_div_assoc, mul_assoc] using mul_pos hLe hpos
  · have hlt := lt_of_le_of_lt hbound' hsmall'
    simpa [mul_div_assoc, mul_assoc] using hlt

theorem a_combined (d Y T : ℝ) :
    a d Y T = -(4 * Y ^ 2 + radius T * (radius T + 2 * d)) /
      (16 * (radius T + d) ^ 2) := by
  by_cases h : radius T + d = 0
  · simp [a, h]
  · unfold a
    field_simp
    ring

theorem field_coordinate_bounds {d : ℝ} (hd : 0 < d) {z : Plane} (hz : z ∈ wedge) :
    -(1 / 8 : ℝ) ≤ a d (z 0) (z 1) ∧ a d (z 0) (z 1) ≤ 0 ∧
      |b d (z 0) (z 1)| ≤ 1 / 4 := by
  have hr := radius_nonneg_of_mem_wedge hz
  have hden := denominator_pos_of_mem_wedge hd hz
  have hw : 2 * |z 0| ≤ radius (z 1) := hz
  have hsq := mul_self_le_mul_self (by positivity : 0 ≤ 2 * |z 0|) hw
  have hYsq : 4 * z 0 ^ 2 ≤ radius (z 1) ^ 2 := by
    nlinarith [sq_abs (z 0)]
  have hn0 : 0 ≤ 4 * z 0 ^ 2 + radius (z 1) * (radius (z 1) + 2 * d) := by
    positivity
  have hn1 : 4 * z 0 ^ 2 + radius (z 1) * (radius (z 1) + 2 * d) ≤
      2 * (radius (z 1) + d) ^ 2 := by
    nlinarith [mul_nonneg hr hd.le, sq_nonneg d]
  have hp16 : 0 < 16 * (radius (z 1) + d) ^ 2 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [a_combined]
    apply (le_div_iff₀ hp16).mpr
    nlinarith
  · rw [a_combined]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hn0) hp16.le
  · unfold b
    rw [abs_div, abs_of_pos (mul_pos (by norm_num) hden)]
    apply (div_le_iff₀ (mul_pos (by norm_num) hden)).mpr
    linarith

theorem field_norm_bound {d : ℝ} (hd : 0 < d) {z : Plane} (hz : z ∈ wedge) :
    ‖field d z‖ ≤ 3 / 8 := by
  obtain ⟨ha0, ha1, hb⟩ := field_coordinate_bounds hd hz
  have ha : |a d (z 0) (z 1)| ≤ 1 / 8 := (abs_le.mpr ⟨ha0, by linarith⟩)
  have hn := plane_norm_le_sum (field d z)
  simp only [field, vec2_zero, vec2_one] at hn
  exact hn.trans (by linarith)

theorem potential_hasDerivAt_Y (d Y T : ℝ) :
    HasDerivAt (fun y => potential d y T) (b d Y T) Y := by
  have hp := (((hasDerivAt_id Y).pow 2).sub_const (radius T ^ 2 / 4)).div_const
    (4 * (radius T + d))
  convert hp using 1 <;> first | rfl |
    (dsimp [potential, b]; simp only [div_eq_mul_inv, mul_inv_rev]; ring)

theorem potential_hasDerivAt_T (d Y T : ℝ) (h : radius T + d ≠ 0) :
    HasDerivAt (fun t => potential d Y t) (-a d Y T) T := by
  have hr := (hasDerivAt_id T).const_sub (1 / 2 : ℝ)
  have hn := (hasDerivAt_const T (Y ^ 2)).sub ((hr.pow 2).div_const 4)
  have hd := (hr.add_const d).const_mul 4
  have h4 : 4 * (1 / 2 - T + d) ≠ 0 := mul_ne_zero (by norm_num) h
  have hp := hn.div hd h4
  convert hp using 1 <;> first | rfl |
    (dsimp [potential, a, radius]; field_simp [show 1 / 2 - T + d ≠ 0 from h]; ring)

theorem wall_plus_factor (d Y T : ℝ) (h : radius T + d ≠ 0) :
    -b d Y T / 2 + a d Y T =
      -(radius T / 2 + Y) * (2 * Y + 2 * d + radius T) /
        (8 * (radius T + d) ^ 2) := by
  unfold a b
  field_simp
  ring

theorem wall_minus_factor (d Y T : ℝ) (h : radius T + d ≠ 0) :
    -b d Y T / 2 - a d Y T =
      (radius T / 2 - Y) * (-2 * Y + 2 * d + radius T) /
        (8 * (radius T + d) ^ 2) := by
  unfold a b
  field_simp
  ring

theorem tilted_wall_plus (d Y T s : ℝ) (h : radius T + d ≠ 0) :
    radius (T + s * b d Y T) / 2 + (Y + s * a d Y T) =
      (radius T / 2 + Y) *
        (1 - s * (2 * Y + 2 * d + radius T) / (8 * (radius T + d) ^ 2)) := by
  calc
    _ = radius T / 2 + Y + s * (-b d Y T / 2 + a d Y T) := by
      unfold radius
      ring
    _ = _ := by rw [wall_plus_factor d Y T h]; ring

theorem tilted_wall_minus (d Y T s : ℝ) (h : radius T + d ≠ 0) :
    radius (T + s * b d Y T) / 2 - (Y + s * a d Y T) =
      (radius T / 2 - Y) *
        (1 + s * (-2 * Y + 2 * d + radius T) / (8 * (radius T + d) ^ 2)) := by
  calc
    _ = radius T / 2 - Y + s * (-b d Y T / 2 - a d Y T) := by
      unfold radius
      ring
    _ = _ := by rw [wall_minus_factor d Y T h]; ring

theorem mem_wedge_iff_walls_nonneg (Y T : ℝ) :
    vec2 Y T ∈ wedge ↔ 0 ≤ radius T / 2 + Y ∧ 0 ≤ radius T / 2 - Y := by
  change 2 * |Y| ≤ radius T ↔ _
  constructor
  · intro h
    constructor <;> linarith [le_abs_self Y, neg_le_abs Y]
  · rintro ⟨h₁, h₂⟩
    have h : |Y| ≤ radius T / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith

theorem tilted_mem_wedge_iff (d Y T s : ℝ) (h : radius T + d ≠ 0)
    (hp : 0 < 1 - s * (2 * Y + 2 * d + radius T) / (8 * (radius T + d) ^ 2))
    (hm : 0 < 1 + s * (-2 * Y + 2 * d + radius T) / (8 * (radius T + d) ^ 2)) :
    vec2 (Y + s * a d Y T) (T + s * b d Y T) ∈ wedge ↔ vec2 Y T ∈ wedge := by
  rw [mem_wedge_iff_walls_nonneg, tilted_wall_plus d Y T s h,
    tilted_wall_minus d Y T s h, mul_nonneg_iff_of_pos_right hp,
    mul_nonneg_iff_of_pos_right hm, mem_wedge_iff_walls_nonneg]

end SlopeRational

end

end OAI
