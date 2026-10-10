import OAI.Geometry.SurfaceImmersion.Primitive.VelocityPlaneCoordinates

namespace OAI

/-! The boundary non-antipodality condition survives projection to the velocity plane. -/
noncomputable section
open scoped Matrix

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame RealModes

lemma no_opposite_ray_of_normalized {B n : Vec} (hB : B ≠ 0)
    (hn : n ⬝ᵥ n = 1) (hanti : normalize B ≠ -n) :
    ∀ r : ℝ, 0 < r → n ≠ -r • B := by
  intro r hr he
  have hp := dot_self_pos hB
  have hs : Real.sqrt (B ⬝ᵥ B) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  have hsq : r ^ 2 * (B ⬝ᵥ B) = 1 := by
    rw [he] at hn
    simpa only [smul_dotProduct, dotProduct_smul, smul_eq_mul, neg_mul_neg,
      ← mul_assoc, ← pow_two, neg_sq] using hn
  have hroot : (r * Real.sqrt (B ⬝ᵥ B)) ^ 2 = 1 := by
    rw [mul_pow, Real.sq_sqrt hp.le, hsq]
  have hpos : 0 < r * Real.sqrt (B ⬝ᵥ B) := mul_pos hr (Real.sqrt_pos.mpr hp)
  have heq : r * Real.sqrt (B ⬝ᵥ B) = 1 := by nlinarith
  have hr' : r = (Real.sqrt (B ⬝ᵥ B))⁻¹ := by
    apply mul_right_cancel₀ hs
    rw [heq, inv_mul_cancel₀ hs]
  apply hanti
  rw [he, neg_smul, neg_neg, hr']
  rfl

lemma projected_second_form {X Y B C : Vec} {a b : ℝ}
    (hD : gramDet Y C ≠ 0) (hC : C = a • X + b • Y + B) :
    realNormalPart Y C B = -a • realNormalPart Y C X := by
  have hlin := realNormalPart_linear Y C
  have he := congrArg (realNormalPart Y C) hC
  rw [realNormalPart_self_right _ _ hD] at he
  simp only [hlin.map_add, hlin.map_smul, realNormalPart_self_left _ _ hD,
    smul_zero, add_zero] at he
  simpa only [neg_smul] using (eq_neg_of_add_eq_zero_right he.symm)

lemma projection_preserves_no_opposite_ray {X Y B C n : Vec} {a b : ℝ}
    (hD : gramDet X Y ≠ 0) (ha : a ≠ 0)
    (hXB : X ⬝ᵥ B = 0) (hYB : Y ⬝ᵥ B = 0)
    (hC : C = a • X + b • Y + B)
    (hXn : X ⬝ᵥ n = 0) (hYn : Y ⬝ᵥ n = 0)
    (hanti : ∀ r : ℝ, 0 < r → n ≠ -r • B) :
    ∀ r : ℝ, 0 < r → realNormalPart Y C B ≠ -r • realNormalPart Y C n := by
  intro r hr hrel
  have hlin := realNormalPart_linear Y C
  have himage : realNormalPart Y C (B + r • n) = 0 := by
    rw [hlin.map_add, hlin.map_smul, hrel]
    simp [neg_smul]
  have hz : B + r • n = 0 := projected_normal_kernel hD ha hXB hYB hC
    (by simp [dotProduct_add, dotProduct_smul, hXB, hXn])
    (by simp [dotProduct_add, dotProduct_smul, hYB, hYn]) himage
  apply hanti (1 / r) (one_div_pos.mpr hr)
  ext i
  have hi : B i + r * n i = 0 := congrFun hz i
  change n i = -(1 / r) * B i
  field_simp [hr.ne']
  linear_combination hi

lemma projected_tangent_no_opposite_ray {X Y B C n : Vec} {a b : ℝ}
    (hD : gramDet X Y ≠ 0) (ha : a < 0)
    (hXB : X ⬝ᵥ B = 0) (hYB : Y ⬝ᵥ B = 0)
    (hC : C = a • X + b • Y + B)
    (hXn : X ⬝ᵥ n = 0) (hYn : Y ⬝ᵥ n = 0)
    (hanti : ∀ r : ℝ, 0 < r → n ≠ -r • B) :
    ∀ r : ℝ, 0 < r → realNormalPart Y C X ≠ -r • realNormalPart Y C n := by
  have hD' := (velocity_gram_pos hD ha.ne hXB hYB hC).ne'
  have hsecond := projected_second_form hD' hC
  intro r hr hx
  have he : realNormalPart Y C B = -((-a) * r) • realNormalPart Y C n := by
    rw [hsecond, hx, smul_smul]
    congr 1
    ring
  exact projection_preserves_no_opposite_ray hD ha.ne hXB hYB hC hXn hYn hanti
    ((-a) * r) (mul_pos (neg_pos.mpr ha) hr) he

end ClosedSurfaceR4.VelocityFrame

end

end OAI
