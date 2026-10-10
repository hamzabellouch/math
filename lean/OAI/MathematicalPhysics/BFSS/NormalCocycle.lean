import Mathlib

namespace OAI

/-! Vanishing normal cocycles for skew Lie triples. -/

namespace BFSSNormal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma skew_sum_sq_kernel (X Y Z : E →ₗ[ℝ] E)
    (hX : ∀ u v, inner ℝ (X u) v = -inner ℝ u (X v))
    (hY : ∀ u v, inner ℝ (Y u) v = -inner ℝ u (Y v))
    (hZ : ∀ u v, inner ℝ (Z u) v = -inner ℝ u (Z v))
    (a : E) (ha : X (X a) + Y (Y a) + Z (Z a) = 0) :
    X a = 0 ∧ Y a = 0 ∧ Z a = 0 := by
  have hh := congrArg (fun v => inner ℝ a v) ha
  simp only [inner_add_right, inner_zero_right] at hh
  have hx := hX a (X a)
  have hy := hY a (Y a)
  have hz := hZ a (Z a)
  rw [real_inner_self_eq_norm_sq] at hx hy hz
  have h0 : ‖X a‖^2 + ‖Y a‖^2 + ‖Z a‖^2 = 0 := by linarith
  have hx0 : ‖X a‖ = 0 := by nlinarith [sq_nonneg ‖Y a‖, sq_nonneg ‖Z a‖]
  have hy0 : ‖Y a‖ = 0 := by nlinarith [sq_nonneg ‖X a‖, sq_nonneg ‖Z a‖]
  have hz0 : ‖Z a‖ = 0 := by nlinarith [sq_nonneg ‖X a‖, sq_nonneg ‖Y a‖]
  exact ⟨norm_eq_zero.mp hx0,norm_eq_zero.mp hy0,norm_eq_zero.mp hz0⟩

lemma cocycle_laplacian (X Y Z : E →ₗ[ℝ] E)
    (hYX : ∀ u, Y (X u) = X (Y u) - (2:ℝ) • Z u)
    (hZX : ∀ u, Z (X u) = X (Z u) + (2:ℝ) • Y u)
    (a b c : E)
    (hab : X b - Y a = (2:ℝ) • c)
    (_hbc : Y c - Z b = (2:ℝ) • a)
    (hca : Z a - X c = (2:ℝ) • b) :
    X (X a) + Y (Y a) + Z (Z a) = X (X a + Y b + Z c) := by
  have hya : Y a = X b - (2:ℝ) • c := by rw [←hab]; abel
  have hza : Z a = X c + (2:ℝ) • b := by rw [←hca]; abel
  rw [hya,hza,map_sub,map_add,map_smul,map_smul,hYX,hZX]
  simp only [map_add]
  module

theorem normal_cocycle_zero (X Y Z : E →ₗ[ℝ] E)
    (hX : ∀ u v, inner ℝ (X u) v = -inner ℝ u (X v))
    (hY : ∀ u v, inner ℝ (Y u) v = -inner ℝ u (Y v))
    (hZ : ∀ u v, inner ℝ (Z u) v = -inner ℝ u (Z v))
    (hXY : ∀ u, X (Y u) - Y (X u) = (2:ℝ) • Z u)
    (hYZ : ∀ u, Y (Z u) - Z (Y u) = (2:ℝ) • X u)
    (hZX : ∀ u, Z (X u) - X (Z u) = (2:ℝ) • Y u)
    (a b c : E)
    (hab : X b - Y a = (2:ℝ) • c)
    (hbc : Y c - Z b = (2:ℝ) • a)
    (hca : Z a - X c = (2:ℝ) • b)
    (hperp : X a + Y b + Z c = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have hYX' (u : E) : Y (X u) = X (Y u) - (2:ℝ) • Z u := by rw [←hXY u]; abel
  have hZY' (u : E) : Z (Y u) = Y (Z u) - (2:ℝ) • X u := by rw [←hYZ u]; abel
  have hXZ' (u : E) : X (Z u) = Z (X u) - (2:ℝ) • Y u := by rw [←hZX u]; abel
  have hZX' (u : E) : Z (X u) = X (Z u) + (2:ℝ) • Y u := by rw [←hZX u]; abel
  have hXY' (u : E) : X (Y u) = Y (X u) + (2:ℝ) • Z u := by rw [←hXY u]; abel
  have hYZ' (u : E) : Y (Z u) = Z (Y u) + (2:ℝ) • X u := by rw [←hYZ u]; abel
  have ha := cocycle_laplacian X Y Z hYX' hZX' a b c hab hbc hca
  rw [hperp,map_zero] at ha
  have hp2 : Y b + Z c + X a = 0 := by rw [←hperp]; abel
  have hp3 : Z c + X a + Y b = 0 := by rw [←hperp]; abel
  have hb := cocycle_laplacian Y Z X hZY' hXY' b c a hbc hca hab
  rw [hp2,map_zero] at hb
  have hc := cocycle_laplacian Z X Y hXZ' hYZ' c a b hca hab hbc
  rw [hp3,map_zero] at hc
  obtain ⟨hxa,hya,hza⟩ := skew_sum_sq_kernel X Y Z hX hY hZ a ha
  obtain ⟨hyb,hzb,hxb⟩ := skew_sum_sq_kernel Y Z X hY hZ hX b hb
  obtain ⟨hzc,hxc,hyc⟩ := skew_sum_sq_kernel Z X Y hZ hX hY c hc
  rw [hxb,hya,sub_self] at hab
  rw [hyc,hzb,sub_self] at hbc
  rw [hza,hxc,sub_self] at hca
  exact ⟨(smul_eq_zero.mp hbc.symm).resolve_left (by norm_num),
    (smul_eq_zero.mp hca.symm).resolve_left (by norm_num),
    (smul_eq_zero.mp hab.symm).resolve_left (by norm_num)⟩
end
end BFSSNormal

end OAI
