import OAI.Geometry.SurfaceImmersion.Primitive.FrozenCircularData
import OAI.Geometry.SurfaceImmersion.Geometry.LocalFlatExtension

namespace OAI

/-! At a boundary where the velocity correction vanishes on the exterior,
the limiting first normal coefficient and normal length are the old ones. -/
noncomputable section
open Set
open scoped ContDiff Matrix

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame RealModes

lemma leadingNormal_at_projection (X Y C : Vec) :
    leadingNormal X Y C (realNormalPart Y C X) = realNormalPart X Y C := by
  simp only [leadingNormal, leadingTangent, sub_add_cancel]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem boundary_normal_match {Q X Y C e₁ e₂ : E → Vec} {R α : E → ℝ} {O U : Set E}
    (hU : IsOpen U) (hO : IsOpen O) (hOU : O ⊆ U)
    (hQ : ContDiffOn ℝ ∞ Q U) (hX : ContDiffOn ℝ ∞ X U)
    (hR : ContDiffOn ℝ ∞ R U) (h₁ : ContDiffOn ℝ ∞ e₁ U)
    (h₂ : ContDiffOn ℝ ∞ e₂ U) (hα : ContDiffOn ℝ ∞ α U)
    (hproj : ∀ x ∈ U, Q x = X x - realNormalPart (Y x) (C x) (X x))
    (hext : ∀ x ∈ O, Q x + R x • direction (e₁ x) (e₂ x) (α x) = X x)
    {x : E} (hx : x ∈ closure O ∩ U) (d : E)
    (hframe : e₁ x ⬝ᵥ e₁ x = 1 ∧ e₂ x ⬝ᵥ e₂ x = 1 ∧ e₁ x ⬝ᵥ e₂ x = 0 ∧
      Y x ⬝ᵥ e₁ x = 0 ∧ C x ⬝ᵥ e₁ x = 0 ∧ Y x ⬝ᵥ e₂ x = 0 ∧ C x ⬝ᵥ e₂ x = 0) :
    frozenFirst Q X Y C R e₁ e₂ d (x, α x) =
      fderiv ℝ X x d ⬝ᵥ normalize (realNormalPart (X x) (Y x) (C x)) ∧
    frozenSize X Y C R e₁ e₂ (x, α x) =
      Real.sqrt (realNormalPart (X x) (Y x) (C x) ⬝ᵥ
        realNormalPart (X x) (Y x) (C x)) := by
  let T : E → Vec := fun y => Q y + R y • direction (e₁ y) (e₂ y) (α y)
  have hT : ContDiffOn ℝ ∞ T U :=
    hQ.add (hR.smul ((hα.cos.smul h₁).add (hα.sin.smul h₂)))
  have hEq : EqOn T X (closure O ∩ U) :=
    (show EqOn T X O from hext).of_subset_closure
      (hT.continuousOn.mono inter_subset_right) (hX.continuousOn.mono inter_subset_right)
      (fun y hy => ⟨subset_closure hy, hOU hy⟩) inter_subset_left
  have hV : R x • direction (e₁ x) (e₂ x) (α x) = realNormalPart (Y x) (C x) (X x) := by
    have he := hEq hx
    change Q x + R x • direction (e₁ x) (e₂ x) (α x) = X x at he
    rw [hproj x hx.2] at he
    have he' := congrArg (fun z => z - (X x - realNormalPart (Y x) (C x) (X x))) he
    simpa only [add_sub_cancel_left, sub_sub_cancel] using he'
  have hN : frozenNormal X Y C R e₁ e₂ (x, α x) =
      normalize (realNormalPart (X x) (Y x) (C x)) := by
    change normalize (leadingNormal (X x) (Y x) (C x) _) = _
    rw [hV, leadingNormal_at_projection]
  constructor
  · have hd := actual_first_eq_frozen (X := X) (d := d)
      ((hQ.contDiffAt (hU.mem_nhds hx.2)).differentiableAt (by simp))
      ((hR.contDiffAt (hU.mem_nhds hx.2)).differentiableAt (by simp))
      ((h₁.contDiffAt (hU.mem_nhds hx.2)).differentiableAt (by simp))
      ((h₂.contDiffAt (hU.mem_nhds hx.2)).differentiableAt (by simp))
      ((hα.contDiffAt (hU.mem_nhds hx.2)).differentiableAt (by simp)) hframe
    rw [← hd, hN]
    exact congrArg (fun A : E →L[ℝ] Vec => A d ⬝ᵥ normalize (realNormalPart (X x) (Y x) (C x)))
      (fderiv_eq_on_local_closure hU hT hX hO hOU hext hx)
  · change Real.sqrt (leadingNormal (X x) (Y x) (C x) _ ⬝ᵥ
      leadingNormal (X x) (Y x) (C x) _) = _
    rw [hV, leadingNormal_at_projection]

end ClosedSurfaceR4.VelocityFrame

end

end OAI
