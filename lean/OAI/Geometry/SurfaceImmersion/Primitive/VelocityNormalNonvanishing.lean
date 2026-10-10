import OAI.Geometry.SurfaceImmersion.Primitive.VelocityPlaneCoordinates

namespace OAI

/-! The old second derivative has a nonzero normal component after changing velocity. -/
noncomputable section
open scoped Matrix

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame RealModes

lemma gram_ne_zero_of_projection {X Y : Vec} {P : Vec → Vec}
    (hP : IsLinearMap ℝ P) (hPY : P Y = 0) (hPX : P X ≠ 0) (hY : Y ≠ 0) :
    gramDet X Y ≠ 0 := by
  have hYY : Y ⬝ᵥ Y ≠ 0 := (dotProduct_self_eq_zero).not.mpr hY
  intro hD
  let W := (Y ⬝ᵥ Y) • X - (X ⬝ᵥ Y) • Y
  have hW : W ⬝ᵥ W = (Y ⬝ᵥ Y) * gramDet X Y := by
    simp only [W, gramDet, sub_dotProduct, dotProduct_sub, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, dotProduct_comm Y X]
    ring
  have hW0 : W = 0 := dotProduct_self_eq_zero.mp (by rw [hW, hD, mul_zero])
  have hpW : (Y ⬝ᵥ Y) • P X = 0 := by
    have he := congrArg P hW0
    simpa only [W, hP.map_sub, hP.map_smul, hPY, smul_zero, sub_zero, hP.map_zero] using he
  exact hPX ((smul_eq_zero.mp hpW).resolve_left hYY)

lemma normalPart_ne_zero_of_projection {X Y C : Vec} {P : Vec → Vec}
    (hP : IsLinearMap ℝ P) (hPY : P Y = 0) (hPC : P C = 0) (hPX : P X ≠ 0)
    (hD : gramDet Y C ≠ 0) : realNormalPart X Y C ≠ 0 := by
  intro hz
  let c := ((Y ⬝ᵥ Y) * (X ⬝ᵥ C) - (X ⬝ᵥ Y) * (Y ⬝ᵥ C)) / gramDet X Y
  let d := ((X ⬝ᵥ X) * (Y ⬝ᵥ C) - (X ⬝ᵥ Y) * (X ⬝ᵥ C)) / gramDet X Y
  have hspan : C = c • X + d • Y := by
    apply sub_eq_zero.mp
    calc
      C - (c • X + d • Y) = C - c • X - d • Y := by abel
      _ = 0 := hz
  have hc : c = 0 := by
    have he := congrArg P hspan
    have he' : c • P X = 0 := by
      simpa only [hPC, hP.map_add, hP.map_smul, hPY, smul_zero, add_zero] using he.symm
    exact (smul_eq_zero.mp he').resolve_right hPX
  have hC : C = d • Y := by simpa only [hc, zero_smul, zero_add] using hspan
  apply hD
  rw [hC]
  simp only [gramDet, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

def leadingTangent (X Y C V : Vec) : Vec := X - realNormalPart Y C X + V

lemma leadingTangent_projection {X Y C V : Vec} (hD : gramDet Y C ≠ 0)
    (hYV : Y ⬝ᵥ V = 0) (hCV : C ⬝ᵥ V = 0) :
    realNormalPart Y C (leadingTangent X Y C V) = V := by
  have hP := realNormalPart_linear Y C
  have hpX := realNormalPart_perp Y C X hD
  change realNormalPart Y C (X - realNormalPart Y C X + V) = V
  rw [hP.map_add, hP.map_sub,
    realNormalPart_of_perp Y C (realNormalPart Y C X) hpX.1 hpX.2,
    realNormalPart_of_perp Y C V hYV hCV, sub_self, zero_add]

/-- Neither the leading tangent pair nor the normal component of `C` degenerates. -/
theorem leading_normal_nondegenerate {X Y C V : Vec} (hD : gramDet Y C ≠ 0)
    (hYV : Y ⬝ᵥ V = 0) (hCV : C ⬝ᵥ V = 0) (hV : V ≠ 0) :
    gramDet (leadingTangent X Y C V) Y ≠ 0 ∧
      realNormalPart (leadingTangent X Y C V) Y C ≠ 0 := by
  have hP := realNormalPart_linear Y C
  have hPY := realNormalPart_self_left Y C hD
  have hPC := realNormalPart_self_right Y C hD
  have hPX : realNormalPart Y C (leadingTangent X Y C V) ≠ 0 := by
    rwa [leadingTangent_projection hD hYV hCV]
  have hY : Y ≠ 0 := by
    intro hz
    apply hD
    simp [gramDet, hz]
  exact ⟨gram_ne_zero_of_projection hP hPY hPX hY,
    normalPart_ne_zero_of_projection hP hPY hPC hPX hD⟩

end ClosedSurfaceR4.VelocityFrame

end

end OAI
