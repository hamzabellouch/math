import OAI.Geometry.SurfaceImmersion.Geometry.ZeroAmplitudeJet
import OAI.Geometry.SurfaceImmersion.Geometry.BoundaryNormalMatch

namespace OAI

/-! The frozen boundary coefficients at zero amplitude are the old mixed
second derivative and old pure normal length. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame RealModes
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma zero_amplitude_boundary_coefficients {X Y C v e₁ e₂ : E → Vec} {a : E → ℝ} {x : E}
    (hX : ContDiffAt ℝ ∞ X x) (hv : ContDiffAt ℝ ∞ v x) (ha : ContDiffAt ℝ ∞ a x)
    (h₁ : ContDiffAt ℝ ∞ e₁ x) (h₂ : ContDiffAt ℝ ∞ e₂ x)
    (hn : v x ≠ 0) (hax : a x = 0)
    (he₁ : e₁ =ᶠ[𝓝 x] fun y => normalize (v y))
    (hproj : v x = realNormalPart (Y x) (C x) (X x))
    (hframe : e₁ x ⬝ᵥ e₁ x = 1 ∧ e₂ x ⬝ᵥ e₂ x = 1 ∧ e₁ x ⬝ᵥ e₂ x = 0 ∧
      Y x ⬝ᵥ e₁ x = 0 ∧ C x ⬝ᵥ e₁ x = 0 ∧ Y x ⬝ᵥ e₂ x = 0 ∧ C x ⬝ᵥ e₂ x = 0)
    (d : E) :
    frozenFirst (X-v) X Y C (fun y => velocityRadius (v y) (a y)) e₁ e₂ d (x,0) =
      fderiv ℝ X x d ⬝ᵥ normalize (realNormalPart (X x) (Y x) (C x)) ∧
    frozenSize X Y C (fun y => velocityRadius (v y) (a y)) e₁ e₂ (x,0) =
      Real.sqrt (realNormalPart (X x) (Y x) (C x) ⬝ᵥ realNormalPart (X x) (Y x) (C x)) := by
  let R := fun y => velocityRadius (v y) (a y)
  have hs : ContDiffAt ℝ ∞ (fun y => v y ⬝ᵥ v y) x :=
    ContDiffAt.sum (fun i _ => (contDiffAt_pi.mp hv i).mul (contDiffAt_pi.mp hv i))
  have hR : ContDiffAt ℝ ∞ R x := (hs.add (ha.pow 2)).sqrt (by
    simpa [hax] using (dot_self_pos hn).ne')
  have hjet := velocityRadius_normalize_jet hv ha hn hax
  have hV : R x • direction (e₁ x) (e₂ x) 0 = realNormalPart (Y x) (C x) (X x) := by
    simpa only [direction,Real.cos_zero,Real.sin_zero,one_smul,zero_smul,add_zero,
      he₁.eq_of_nhds,← hproj] using hjet.1
  have hsmall : (fun y => R y • e₁ y) =ᶠ[𝓝 x] (fun y => R y • normalize (v y)) := by
    filter_upwards [he₁] with y hy
    rw [hy]
  have hd : fderiv ℝ (fun y => R y • e₁ y) x = fderiv ℝ v x :=
    hsmall.fderiv_eq.trans hjet.2
  have hT : fderiv ℝ (fun y => X y-v y + R y • direction (e₁ y) (e₂ y) 0) x = fderiv ℝ X x := by
    simp only [direction,Real.cos_zero,Real.sin_zero,one_smul,zero_smul,add_zero]
    rw [fderiv_fun_add (f := fun y => X y-v y) (g := fun y => R y • e₁ y) ((hX.sub hv).differentiableAt (by simp))
      ((hR.smul h₁).differentiableAt (by simp)),
      fderiv_fun_sub (hX.differentiableAt (by simp)) (hv.differentiableAt (by simp)),hd,sub_add_cancel]
  have hN : frozenNormal X Y C R e₁ e₂ (x,0) =
      normalize (realNormalPart (X x) (Y x) (C x)) := by
    change normalize (leadingNormal (X x) (Y x) (C x) _) = _
    rw [hV,leadingNormal_at_projection]
  constructor
  · have hf := actual_first_eq_frozen (Q := X-v) (X := X) (Y := Y) (C := C) (R := R)
      (e₁ := e₁) (e₂ := e₂) (α := fun _ => 0) (d := d)
      ((hX.sub hv).differentiableAt (by simp)) (hR.differentiableAt (by simp))
      (h₁.differentiableAt (by simp)) (h₂.differentiableAt (by simp)) (differentiableAt_const 0) hframe
    rw [← hf,hN]
    exact congrArg (fun A : E →L[ℝ] Vec => A d ⬝ᵥ normalize (realNormalPart (X x) (Y x) (C x))) hT
  · change Real.sqrt (leadingNormal (X x) (Y x) (C x) _ ⬝ᵥ
      leadingNormal (X x) (Y x) (C x) _) = _
    rw [hV,leadingNormal_at_projection]

end ClosedSurfaceR4.VelocityFrame

end

end OAI
