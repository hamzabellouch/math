import OAI.Analysis.SphereIsometry.Basic

namespace OAI

/-!
# Aligned sphere chords

The record retains the four actual endpoint equations. Its inverse exchanges the
endpoints and negates the two direction vectors literally; it uses no oddness
property of the sphere isometry.
-/

noncomputable section

namespace Tingley

universe u v

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

structure AlignedConfiguration
    (f : UnitSphere X ≃ᵢ UnitSphere Y) (y : UnitSphere X) (t M : ℝ) where
  x : UnitSphere X
  z : UnitSphere X
  v : UnitSphere X
  w : UnitSphere Y
  p : ℝ
  r : ℝ
  s : ℝ
  u : ℝ
  p_pos : 0 < p
  r_pos : 0 < r
  s_pos : 0 < s
  u_pos : 0 < u
  x_eq : (x : X) = t • (y : X) + p • (v : X)
  z_eq : (z : X) = t • (y : X) - r • (v : X)
  fx_eq : (f x : Y) = t • (f y : Y) + s • (w : Y)
  fz_eq : (f z : Y) = t • (f y : Y) - u • (w : Y)
  s_sub_p : s - p = M
  r_sub_u : r - u = M
  chord_sum : p + r = s + u
  chord_le_two : p + r ≤ 2

theorem unit_radius_bounds_of_norm_sub
    (x y : UnitSphere X) {t p : ℝ} (ht : 0 ≤ t)
    (hd : ‖(x : X) - t • (y : X)‖ = p) :
    1 - t ≤ p ∧ p ≤ 1 + t := by
  have hty : ‖t • (y : X)‖ = t := by
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht,
      UnitSphere.norm_coe, mul_one]
  constructor
  · simpa only [UnitSphere.norm_coe, hty, hd] using
      norm_sub_norm_le (x : X) (t • (y : X))
  · simpa only [UnitSphere.norm_coe, hty, hd] using
      norm_sub_le (x : X) (t • (y : X))

theorem unit_radius_bounds_of_eq_add
    (x y v : UnitSphere X) {t p : ℝ} (ht : 0 ≤ t) (hp : 0 ≤ p)
    (hx : (x : X) = t • (y : X) + p • (v : X)) :
    1 - t ≤ p ∧ p ≤ 1 + t := by
  have hv : (x : X) - t • (y : X) = p • (v : X) := by
    rw [hx]
    abel
  have hd : ‖(x : X) - t • (y : X)‖ = p := by
    rw [hv]
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hp,
      UnitSphere.norm_coe, mul_one]
  exact unit_radius_bounds_of_norm_sub x y ht hd

theorem unit_radius_bounds_of_eq_sub
    (x y v : UnitSphere X) {t p : ℝ} (ht : 0 ≤ t) (hp : 0 ≤ p)
    (hx : (x : X) = t • (y : X) - p • (v : X)) :
    1 - t ≤ p ∧ p ≤ 1 + t := by
  have hv : (x : X) - t • (y : X) = -(p • (v : X)) := by
    rw [hx]
    abel
  have hd : ‖(x : X) - t • (y : X)‖ = p := by
    rw [hv, norm_neg]
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hp,
      UnitSphere.norm_coe, mul_one]
  exact unit_radius_bounds_of_norm_sub x y ht hd

namespace AlignedConfiguration

variable {f : UnitSphere X ≃ᵢ UnitSphere Y} {y : UnitSphere X} {t M : ℝ}
variable (C : AlignedConfiguration f y t M)

def d : ℝ := C.p + C.r

def A : ℝ := C.p / C.d

def B : ℝ := C.u / C.d

theorem d_pos : 0 < C.d := add_pos C.p_pos C.r_pos

theorem d_ne_zero : C.d ≠ 0 := ne_of_gt C.d_pos

theorem d_le_two : C.d ≤ 2 := C.chord_le_two

theorem d_eq_s_add_u : C.d = C.s + C.u := C.chord_sum

theorem A_pos : 0 < C.A := div_pos C.p_pos C.d_pos

theorem B_pos : 0 < C.B := div_pos C.u_pos C.d_pos

theorem A_lt_one : C.A < 1 := by
  apply (div_lt_one C.d_pos).2
  dsimp only [d]
  linarith [C.r_pos]

theorem B_lt_one : C.B < 1 := by
  apply (div_lt_one C.d_pos).2
  rw [C.d_eq_s_add_u]
  linarith [C.s_pos]

theorem A_add_B : C.A + C.B = 1 - M / C.d := by
  dsimp only [A, B]
  rw [← add_div, eq_sub_iff_add_eq, ← add_div]
  have hsum : C.p + C.u + M = C.d := by
    dsimp only [d]
    linarith [C.r_sub_u]
  rw [hsum, div_self C.d_ne_zero]

theorem A_add_B_lt_one (hM : 0 < M) : C.A + C.B < 1 := by
  rw [C.A_add_B]
  have hMd := div_pos hM C.d_pos
  linarith

theorem one_sub_B : 1 - C.B = C.s / C.d := by
  apply (eq_div_iff C.d_ne_zero).2
  dsimp only [B]
  rw [sub_mul, one_mul, div_mul_cancel₀ _ C.d_ne_zero, C.d_eq_s_add_u]
  ring

theorem one_sub_A : 1 - C.A = C.r / C.d := by
  apply (eq_div_iff C.d_ne_zero).2
  dsimp only [A]
  rw [sub_mul, one_mul, div_mul_cancel₀ _ C.d_ne_zero]
  dsimp only [d]
  ring

theorem p_eq_d_mul_A : C.p = C.d * C.A := by
  simpa only [A, mul_comm] using (div_mul_cancel₀ C.p C.d_ne_zero).symm

theorem u_eq_d_mul_B : C.u = C.d * C.B := by
  simpa only [B, mul_comm] using (div_mul_cancel₀ C.u C.d_ne_zero).symm

theorem chord_identity : C.s * C.r - C.u * C.p = M * C.d := by
  calc
    C.s * C.r - C.u * C.p = (C.s - C.p) * C.r + C.p * (C.r - C.u) := by ring
    _ = M * C.r + C.p * M := by rw [C.s_sub_p, C.r_sub_u]
    _ = M * C.d := by dsimp only [d]; ring

theorem norm_x_sub_z : ‖(C.x : X) - (C.z : X)‖ = C.d := by
  have he : (C.x : X) - (C.z : X) = C.d • (C.v : X) := by
    rw [C.x_eq, C.z_eq]
    dsimp only [d]
    rw [add_smul]
    abel
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos C.d_pos,
    UnitSphere.norm_coe, mul_one]

theorem p_bounds (ht : 0 ≤ t) : 1 - t ≤ C.p ∧ C.p ≤ 1 + t :=
  unit_radius_bounds_of_eq_add C.x y C.v ht C.p_pos.le C.x_eq

theorem r_bounds (ht : 0 ≤ t) : 1 - t ≤ C.r ∧ C.r ≤ 1 + t :=
  unit_radius_bounds_of_eq_sub C.z y C.v ht C.r_pos.le C.z_eq

theorem s_bounds (ht : 0 ≤ t) : 1 - t ≤ C.s ∧ C.s ≤ 1 + t :=
  unit_radius_bounds_of_eq_add (f C.x) (f y) C.w ht C.s_pos.le C.fx_eq

theorem u_bounds (ht : 0 ≤ t) : 1 - t ≤ C.u ∧ C.u ≤ 1 + t :=
  unit_radius_bounds_of_eq_sub (f C.z) (f y) C.w ht C.u_pos.le C.fz_eq

/-- Exchange the endpoints and literally negate both chord directions. -/
def inverse : AlignedConfiguration f.symm (f y) t M where
  x := f C.z
  z := f C.x
  v := ⟨-(C.w : Y), by simp⟩
  w := ⟨-(C.v : X), by simp⟩
  p := C.u
  r := C.s
  s := C.r
  u := C.p
  p_pos := C.u_pos
  r_pos := C.s_pos
  s_pos := C.r_pos
  u_pos := C.p_pos
  x_eq := by simpa only [smul_neg, sub_eq_add_neg] using C.fz_eq
  z_eq := by simpa only [smul_neg, sub_neg_eq_add] using C.fx_eq
  fx_eq := by
    simpa only [IsometryEquiv.symm_apply_apply, smul_neg, sub_eq_add_neg] using C.z_eq
  fz_eq := by
    simpa only [IsometryEquiv.symm_apply_apply, smul_neg, sub_neg_eq_add] using C.x_eq
  s_sub_p := C.r_sub_u
  r_sub_u := C.s_sub_p
  chord_sum := by linarith [C.chord_sum]
  chord_le_two := by linarith [C.chord_sum, C.chord_le_two]

@[simp] theorem inverse_x : C.inverse.x = f C.z := rfl

@[simp] theorem inverse_z : C.inverse.z = f C.x := rfl

@[simp] theorem inverse_v_coe : (C.inverse.v : Y) = -(C.w : Y) := rfl

@[simp] theorem inverse_w_coe : (C.inverse.w : X) = -(C.v : X) := rfl

@[simp] theorem inverse_p : C.inverse.p = C.u := rfl

@[simp] theorem inverse_r : C.inverse.r = C.s := rfl

@[simp] theorem inverse_s : C.inverse.s = C.r := rfl

@[simp] theorem inverse_u : C.inverse.u = C.p := rfl

@[simp] theorem inverse_d : C.inverse.d = C.d := by
  change C.u + C.s = C.p + C.r
  linarith [C.chord_sum]

@[simp] theorem inverse_A : C.inverse.A = C.B := by
  simp only [A, B, inverse_p, inverse_d]

@[simp] theorem inverse_B : C.inverse.B = C.A := by
  simp only [A, B, inverse_u, inverse_d]

end AlignedConfiguration

end Tingley

end

end OAI
