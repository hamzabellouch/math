import OAI.Geometry.SurfaceImmersion.Primitive.VelocityCircleLift

namespace OAI

/-! Coordinates in the actual two-dimensional velocity plane. -/
noncomputable section
open scoped Matrix

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame

lemma velocity_frame_independent {Y C e₁ e₂ : Vec}
    (hD : gramDet Y C ≠ 0) (h₁ : e₁ ⬝ᵥ e₁ = 1) (h₂ : e₂ ⬝ᵥ e₂ = 1)
    (h12 : e₁ ⬝ᵥ e₂ = 0) (hY1 : Y ⬝ᵥ e₁ = 0) (hY2 : Y ⬝ᵥ e₂ = 0)
    (hC1 : C ⬝ᵥ e₁ = 0) (hC2 : C ⬝ᵥ e₂ = 0) :
    LinearIndependent ℝ ![Y, C, e₁, e₂] := by
  apply Fintype.linearIndependent_iff.mpr
  intro a ha
  have he : a 0 • Y + (a 1 • C + (a 2 • e₁ + a 3 • e₂)) = 0 := by
    simpa [Fin.sum_univ_succ] using ha
  have hy := congrArg (fun w => Y ⬝ᵥ w) he
  have hc := congrArg (fun w => C ⬝ᵥ w) he
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, hY1, hY2, hC1, hC2,
    mul_zero, add_zero, dotProduct_zero, dotProduct_comm C Y] at hy hc
  have haD : a 0 * gramDet Y C = 0 := by
    unfold gramDet
    linear_combination (C ⬝ᵥ C) * hy - (Y ⬝ᵥ C) * hc
  have hbD : a 1 * gramDet Y C = 0 := by
    unfold gramDet
    linear_combination (Y ⬝ᵥ Y) * hc - (Y ⬝ᵥ C) * hy
  have ha0 := (mul_eq_zero.mp haD).resolve_right hD
  have ha1 := (mul_eq_zero.mp hbD).resolve_right hD
  have hz : a 2 • e₁ + a 3 • e₂ = 0 := by simpa [ha0, ha1] using he
  have h2 := congrArg (fun w => e₁ ⬝ᵥ w) hz
  have h3 := congrArg (fun w => e₂ ⬝ᵥ w) hz
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, h₁, h₂, h12,
    dotProduct_comm e₂ e₁, mul_one, mul_zero, add_zero, zero_add, dotProduct_zero] at h2 h3
  intro i
  fin_cases i
  · exact ha0
  · exact ha1
  · exact h2
  · exact h3

lemma orthogonal_frame_eq_zero {Y C e₁ e₂ w : Vec}
    (hlin : LinearIndependent ℝ ![Y, C, e₁, e₂])
    (hY : Y ⬝ᵥ w = 0) (hC : C ⬝ᵥ w = 0)
    (h1 : e₁ ⬝ᵥ w = 0) (h2 : e₂ ⬝ᵥ w = 0) : w = 0 := by
  have hs := hlin.span_eq_top_of_card_eq_finrank (by simp [Vec])
  have hw : w ∈ Submodule.span ℝ (Set.range ![Y, C, e₁, e₂]) := by
    rw [hs]
    trivial
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hw
  apply dotProduct_self_eq_zero.mp
  calc
    w ⬝ᵥ w = (∑ i, a i • (![Y, C, e₁, e₂] i)) ⬝ᵥ w := by rw [ha]
    _ = 0 := by simp [Fin.sum_univ_succ, add_dotProduct, smul_dotProduct, hY, hC, h1, h2]

def planeCoordinates (e₁ e₂ v : Vec) : LoopDensity.Plane := ![v ⬝ᵥ e₁, v ⬝ᵥ e₂]

theorem plane_coordinates_reconstruct {Y C e₁ e₂ v : Vec}
    (hD : gramDet Y C ≠ 0) (h₁ : e₁ ⬝ᵥ e₁ = 1) (h₂ : e₂ ⬝ᵥ e₂ = 1)
    (h12 : e₁ ⬝ᵥ e₂ = 0) (hY1 : Y ⬝ᵥ e₁ = 0) (hY2 : Y ⬝ᵥ e₂ = 0)
    (hC1 : C ⬝ᵥ e₁ = 0) (hC2 : C ⬝ᵥ e₂ = 0)
    (hYv : Y ⬝ᵥ v = 0) (hCv : C ⬝ᵥ v = 0) :
    planeLift e₁ e₂ (planeCoordinates e₁ e₂ v) = v := by
  apply sub_eq_zero.mp
  apply orthogonal_frame_eq_zero (velocity_frame_independent hD h₁ h₂ h12 hY1 hY2 hC1 hC2)
  all_goals simp [planeLift_apply, planeCoordinates, dotProduct_sub, dotProduct_add,
    dotProduct_smul, hY1, hY2, hC1, hC2, hYv, hCv, h₁, h₂, h12,
    dotProduct_comm e₂ e₁, dotProduct_comm e₁ v, dotProduct_comm e₂ v]

lemma plane_coordinates_length {Y C e₁ e₂ v : Vec}
    (hD : gramDet Y C ≠ 0) (h₁ : e₁ ⬝ᵥ e₁ = 1) (h₂ : e₂ ⬝ᵥ e₂ = 1)
    (h12 : e₁ ⬝ᵥ e₂ = 0) (hY1 : Y ⬝ᵥ e₁ = 0) (hY2 : Y ⬝ᵥ e₂ = 0)
    (hC1 : C ⬝ᵥ e₁ = 0) (hC2 : C ⬝ᵥ e₂ = 0)
    (hYv : Y ⬝ᵥ v = 0) (hCv : C ⬝ᵥ v = 0) :
    (v ⬝ᵥ e₁) ^ 2 + (v ⬝ᵥ e₂) ^ 2 = v ⬝ᵥ v := by
  have hr := plane_coordinates_reconstruct hD h₁ h₂ h12 hY1 hY2 hC1 hC2 hYv hCv
  have hd := congrArg (fun w => w ⬝ᵥ w) hr
  simpa [planeLift_apply, planeCoordinates, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, h₁, h₂, h12, dotProduct_comm e₂ e₁, pow_two] using hd

end ClosedSurfaceR4.VelocityFrame

end

end OAI
