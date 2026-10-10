import OAI.MathematicalPhysics.DefocusingNLS.Certificates.HighAngularRay
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

namespace OAI

/-! Geometry and positivity on the initial arc of the high-angular contour. -/

namespace DefocusingNLS

noncomputable def highArcAngle : ℝ := Real.arccos (99/101)
noncomputable def highArcU (θ : ℝ) : ℝ := Real.sin θ/2
noncomputable def highArcV (Z θ : ℝ) : ℝ := Z+(1-Real.cos θ)/2
noncomputable def highArcL (Z θ : ℝ) : ℝ :=
  highArcU θ*(Real.cos θ^2-Real.sin θ^2)+
    highArcV Z θ*(2*Real.sin θ*Real.cos θ)
noncomputable def highArcN (Z θ : ℝ) : ℝ :=
  highArcU θ*(2*Real.sin θ*Real.cos θ)-
    highArcV Z θ*(Real.cos θ^2-Real.sin θ^2)

private theorem highArc_sin_cos (θ : ℝ) (hθ : 0 ≤ θ) (hθ' : θ ≤ highArcAngle) :
    0 ≤ Real.sin θ ∧ Real.sin θ ≤ 20/101 ∧
      99/101 ≤ Real.cos θ ∧ Real.cos θ ≤ 1 := by
  have hA : highArcAngle ≤ Real.pi/2 := Real.arccos_le_pi_div_two.mpr (by norm_num)
  have hsin : Real.sin highArcAngle = 20/101 := by
    rw [highArcAngle,Real.sin_arccos]
    norm_num
  have hcos : Real.cos highArcAngle = 99/101 :=
    Real.cos_arccos (by norm_num) (by norm_num)
  refine ⟨Real.sin_nonneg_of_nonneg_of_le_pi hθ
      (hθ'.trans (Real.arccos_le_pi _)), ?_, ?_, Real.cos_le_one θ⟩
  · rw [← hsin]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hA hθ'
  · rw [← hcos]
    exact Real.cos_le_cos_of_nonneg_of_le_pi hθ (Real.arccos_le_pi _) hθ'

theorem highArc_geometry (Z θ : ℝ) (hZ : 2704/1000 ≤ Z)
    (hθ : 0 ≤ θ) (hθ' : θ ≤ highArcAngle) :
    0 ≤ highArcU θ ∧ 0 < highArcV Z θ ∧
      0 ≤ highArcL Z θ ∧ highArcN Z θ ≤ -(2444/1000) ∧
      107/10 < Real.cos θ-4*highArcN Z θ := by
  obtain ⟨hs,hs',hc,hc'⟩ := highArc_sin_cos θ hθ hθ'
  have hc0 : 0 ≤ Real.cos θ := by linarith
  have hsc := Real.sin_sq_add_cos_sq θ
  have hS0 : 0 ≤ 2*Real.sin θ*Real.cos θ := by positivity
  have hS1 : 2*Real.sin θ*Real.cos θ ≤ 2/5 := by
    have hm := mul_le_mul_of_nonneg_left hc' hs
    nlinarith
  have hC0 : 92/100 ≤ Real.cos θ^2-Real.sin θ^2 := by
    have hsq : Real.sin θ^2 ≤ (20/101 : ℝ)^2 :=
      (sq_le_sq₀ hs (by norm_num)).mpr hs'
    nlinarith
  have hu : 0 ≤ highArcU θ := by dsimp [highArcU]; positivity
  have hu' : highArcU θ ≤ 1/10 := by dsimp [highArcU]; linarith
  have hv : 27/10 < highArcV Z θ := by dsimp [highArcV]; linarith
  have hv0 : 0 < highArcV Z θ := by linarith
  have hL : 0 ≤ highArcL Z θ := by
    unfold highArcL
    exact add_nonneg (mul_nonneg hu (by linarith)) (mul_nonneg hv0.le hS0)
  have hN : highArcN Z θ ≤ -(2444/1000) := by
    have hfirst := mul_le_mul hu' hS1 hS0 (by norm_num)
    have hsecond := mul_le_mul (le_of_lt hv) hC0 (by norm_num) hv0.le
    unfold highArcN
    nlinarith
  exact ⟨hu,hv0,hL,hN,by linarith⟩

noncomputable def highArcPotential (σ M Z θ : ℝ) : ℝ :=
  σ-3+highArcU θ/4+
    M^2*highArcU θ/(4*(highArcU θ^2+highArcV Z θ^2))+
    Real.sin θ+(3/10)*(Real.cos θ-4*highArcN Z θ)+(3-9/100)*highArcL Z θ

theorem highArcPotential_pos (σ M Z θ : ℝ) (hσ : -(1/32 : ℝ) ≤ σ)
    (hZ : 2704/1000 ≤ Z)
    (hθ : 0 ≤ θ) (hθ' : θ ≤ highArcAngle) :
    0 < highArcPotential σ M Z θ := by
  obtain ⟨hu,hv,hL,_,hL'⟩ := highArc_geometry Z θ hZ hθ hθ'
  have hs := (highArc_sin_cos θ hθ hθ').1
  have hterm : 0 ≤ M^2*highArcU θ/(4*(highArcU θ^2+highArcV Z θ^2)) := by positivity
  unfold highArcPotential
  linarith

theorem highArc_join_L (Z : ℝ) : highArcL Z highArcAngle = highRayL Z 0 := by
  norm_num [highArcL,highArcU,highArcV,highArcAngle,Real.sin_arccos,
    highRayL,highRayU,highRayV]
  rw [Real.cos_arccos (by norm_num) (by norm_num)]
  ring

theorem highArc_join_jump_pos (Z : ℝ) (hZ : 2704/1000 ≤ Z) (hZ' : Z ≤ 2706/1000) :
    0 < -3/2-(3/10)*highArcL Z highArcAngle-highArcN Z highArcAngle := by
  have hN := (highArc_geometry Z highArcAngle hZ (Real.arccos_nonneg _) le_rfl).2.2.2.1
  have hL : highArcL Z highArcAngle < 119/100 := by
    rw [highArc_join_L]
    norm_num [highRayL,highRayU,highRayV]
    linarith
  linarith

end DefocusingNLS

end OAI
