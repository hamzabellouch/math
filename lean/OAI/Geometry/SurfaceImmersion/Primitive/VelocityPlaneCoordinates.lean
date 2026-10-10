import OAI.Geometry.SurfaceImmersion.Primitive.VelocityFrame

namespace OAI

/-! Coordinate nondegeneracy of the moving velocity plane and its normal projection. -/
noncomputable section
open scoped Matrix

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame RealModes

lemma velocity_gram_formula {X Y B C : Vec} {a b : ℝ}
    (hXB : X ⬝ᵥ B = 0) (hYB : Y ⬝ᵥ B = 0)
    (hC : C = a • X + b • Y + B) :
    gramDet Y C = a ^ 2 * gramDet X Y + (Y ⬝ᵥ Y) * (B ⬝ᵥ B) := by
  rw [hC]
  simp only [gramDet, dotProduct_add, add_dotProduct, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, dotProduct_comm B X, dotProduct_comm B Y, dotProduct_comm Y X,
    hXB, hYB, mul_zero, add_zero, zero_add]
  ring

lemma velocity_gram_pos {X Y B C : Vec} {a b : ℝ}
    (hD : gramDet X Y ≠ 0) (ha : a ≠ 0)
    (hXB : X ⬝ᵥ B = 0) (hYB : Y ⬝ᵥ B = 0)
    (hC : C = a • X + b • Y + B) : 0 < gramDet Y C := by
  rw [velocity_gram_formula hXB hYB hC]
  exact add_pos_of_pos_of_nonneg (mul_pos (sq_pos_of_ne_zero ha) (gramDet_pos hD))
    (mul_nonneg (Finset.sum_nonneg (fun i _ => mul_self_nonneg (Y i)))
      (Finset.sum_nonneg (fun i _ => mul_self_nonneg (B i))))

lemma projected_normal_kernel {X Y B C n : Vec} {a b : ℝ}
    (hD : gramDet X Y ≠ 0) (ha : a ≠ 0)
    (hXB : X ⬝ᵥ B = 0) (hYB : Y ⬝ᵥ B = 0)
    (hC : C = a • X + b • Y + B)
    (hXn : X ⬝ᵥ n = 0) (hYn : Y ⬝ᵥ n = 0)
    (hp : realNormalPart Y C n = 0) : n = 0 := by
  let c := ((C ⬝ᵥ C) * (Y ⬝ᵥ n) - (Y ⬝ᵥ C) * (C ⬝ᵥ n)) / gramDet Y C
  let d := ((Y ⬝ᵥ Y) * (C ⬝ᵥ n) - (Y ⬝ᵥ C) * (Y ⬝ᵥ n)) / gramDet Y C
  have hspan : n = c • Y + d • C := by
    apply sub_eq_zero.mp
    calc
      n - (c • Y + d • C) = n - c • Y - d • C := by abel
      _ = 0 := hp
  have hx : c * (X ⬝ᵥ Y) + d * (a * (X ⬝ᵥ X) + b * (X ⬝ᵥ Y)) = 0 := by
    have he := congrArg (fun w => X ⬝ᵥ w) hspan
    rw [hXn, hC] at he
    simpa only [dotProduct_add, dotProduct_smul, smul_eq_mul, hXB, add_zero] using he.symm
  have hy : c * (Y ⬝ᵥ Y) + d * (a * (X ⬝ᵥ Y) + b * (Y ⬝ᵥ Y)) = 0 := by
    have he := congrArg (fun w => Y ⬝ᵥ w) hspan
    rw [hYn, hC] at he
    simpa only [dotProduct_add, dotProduct_smul, smul_eq_mul, hYB, add_zero,
      dotProduct_comm Y X] using he.symm
  have hd : d * a * gramDet X Y = 0 := by
    unfold gramDet
    linear_combination (Y ⬝ᵥ Y) * hx - (X ⬝ᵥ Y) * hy
  have hd0 : d = 0 := (mul_eq_zero.mp ((mul_eq_zero.mp hd).resolve_right hD)).resolve_right ha
  have hYY : Y ⬝ᵥ Y ≠ 0 := by
    intro hz
    have hY : Y = 0 := dotProduct_self_eq_zero.mp hz
    apply hD
    simp [gramDet, hY]
  have hc0 : c = 0 := by
    rw [hd0, zero_mul, add_zero] at hy
    exact (mul_eq_zero.mp hy).resolve_right hYY
  simpa only [hc0, hd0, zero_smul, add_zero] using hspan

lemma projected_normal_ne_zero {X Y B C n : Vec} {a b : ℝ}
    (hD : gramDet X Y ≠ 0) (ha : a ≠ 0)
    (hXB : X ⬝ᵥ B = 0) (hYB : Y ⬝ᵥ B = 0)
    (hC : C = a • X + b • Y + B)
    (hXn : X ⬝ᵥ n = 0) (hYn : Y ⬝ᵥ n = 0) (hn : n ≠ 0) :
    realNormalPart Y C n ≠ 0 :=
  fun hp => hn (projected_normal_kernel hD ha hXB hYB hC hXn hYn hp)

end ClosedSurfaceR4.VelocityFrame

end

end OAI
