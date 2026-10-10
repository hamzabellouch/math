import OAI.Geometry.SurfaceImmersion.Primitive.VelocityCoordinateData
import OAI.Geometry.SurfaceImmersion.Primitive.VelocitySpatialDerivative

namespace OAI

/-! The normal data as smooth functions of position and angular value.
The first mixed normal coefficient contains no derivative of the angle. -/
noncomputable section
open Set
open scoped ContDiff Matrix

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def frozenError (Q : E → Vec) (R : E → ℝ) (e₁ e₂ : E → Vec) (d : E)
    (z : E × ℝ) : Vec :=
  fderiv ℝ Q z.1 d + (fderiv ℝ R z.1 d) • direction (e₁ z.1) (e₂ z.1) z.2 +
    R z.1 • (Real.cos z.2 • fderiv ℝ e₁ z.1 d + Real.sin z.2 • fderiv ℝ e₂ z.1 d)

def frozenNormal (X Y C : E → Vec) (R : E → ℝ) (e₁ e₂ : E → Vec)
    (z : E × ℝ) : Vec :=
  normalize (leadingNormal (X z.1) (Y z.1) (C z.1)
    (R z.1 • direction (e₁ z.1) (e₂ z.1) z.2))

def frozenSize (X Y C : E → Vec) (R : E → ℝ) (e₁ e₂ : E → Vec)
    (z : E × ℝ) : ℝ :=
  normalSize (X z.1) (Y z.1) (C z.1) (R z.1 • direction (e₁ z.1) (e₂ z.1) z.2)

def frozenFirst (Q X Y C : E → Vec) (R : E → ℝ) (e₁ e₂ : E → Vec) (d : E)
    (z : E × ℝ) : ℝ := frozenError Q R e₁ e₂ d z ⬝ᵥ frozenNormal X Y C R e₁ e₂ z

lemma frozenError_smoothOn {Q e₁ e₂ : E → Vec} {R : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hQ : ContDiffOn ℝ ∞ Q U) (hR : ContDiffOn ℝ ∞ R U)
    (h₁ : ContDiffOn ℝ ∞ e₁ U) (h₂ : ContDiffOn ℝ ∞ e₂ U) (d : E) :
    ContDiffOn ℝ ∞ (frozenError Q R e₁ e₂ d) (U ×ˢ univ) := by
  have hDQ : ContDiffOn ℝ ∞ (fun z : E × ℝ => fderiv ℝ Q z.1 d) (U ×ˢ univ) :=
    ((hQ.fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply contDiffOn_const).comp
    contDiffOn_fst (fun z hz => hz.1)
  have hDR : ContDiffOn ℝ ∞ (fun z : E × ℝ => fderiv ℝ R z.1 d) (U ×ˢ univ) :=
    ((hR.fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply contDiffOn_const).comp
    contDiffOn_fst (fun z hz => hz.1)
  have hD₁ : ContDiffOn ℝ ∞ (fun z : E × ℝ => fderiv ℝ e₁ z.1 d) (U ×ˢ univ) :=
    ((h₁.fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply contDiffOn_const).comp
    contDiffOn_fst (fun z hz => hz.1)
  have hD₂ : ContDiffOn ℝ ∞ (fun z : E × ℝ => fderiv ℝ e₂ z.1 d) (U ×ˢ univ) :=
    ((h₂.fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply contDiffOn_const).comp
    contDiffOn_fst (fun z hz => hz.1)
  exact (hDQ.add (hDR.smul
    ((contDiffOn_snd.cos.smul (h₁.comp contDiffOn_fst (fun z hz => hz.1))).add
      (contDiffOn_snd.sin.smul (h₂.comp contDiffOn_fst (fun z hz => hz.1)))))).add
    ((hR.comp contDiffOn_fst (fun z hz => hz.1)).smul
      ((contDiffOn_snd.cos.smul hD₁).add (contDiffOn_snd.sin.smul hD₂)))

theorem frozen_normals_smoothOn {X Y C e₁ e₂ : E → Vec} {R : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hX : ContDiffOn ℝ ∞ X U) (hY : ContDiffOn ℝ ∞ Y U)
    (hC : ContDiffOn ℝ ∞ C U) (hR : ContDiffOn ℝ ∞ R U)
    (h₁ : ContDiffOn ℝ ∞ e₁ U) (h₂ : ContDiffOn ℝ ∞ e₂ U)
    (hD : ∀ x ∈ U, gramDet (Y x) (C x) ≠ 0)
    (hframe : ∀ x ∈ U, e₁ x ⬝ᵥ e₁ x = 1 ∧ e₂ x ⬝ᵥ e₂ x = 1 ∧ e₁ x ⬝ᵥ e₂ x = 0 ∧
      Y x ⬝ᵥ e₁ x = 0 ∧ C x ⬝ᵥ e₁ x = 0 ∧ Y x ⬝ᵥ e₂ x = 0 ∧ C x ⬝ᵥ e₂ x = 0)
    (hR0 : ∀ x ∈ U, R x ≠ 0) :
    ContDiffOn ℝ ∞ (frozenNormal X Y C R e₁ e₂) (U ×ˢ univ) ∧
      ContDiffOn ℝ ∞ (frozenSize X Y C R e₁ e₂) (U ×ˢ univ) := by
  let V : E × ℝ → Vec := fun z => R z.1 • direction (e₁ z.1) (e₂ z.1) z.2
  have hV : ContDiffOn ℝ ∞ V (U ×ˢ univ) :=
    (hR.comp contDiffOn_fst (fun z hz => hz.1)).smul
      ((contDiffOn_snd.cos.smul (h₁.comp contDiffOn_fst (fun z hz => hz.1))).add
        (contDiffOn_snd.sin.smul (h₂.comp contDiffOn_fst (fun z hz => hz.1))))
  have hVY (z : E × ℝ) (hz : z ∈ U ×ˢ (univ : Set ℝ)) : Y z.1 ⬝ᵥ V z = 0 := by
    have hf := hframe z.1 hz.1
    simp [V, direction, dotProduct_add, dotProduct_smul, hf.2.2.2.1, hf.2.2.2.2.2.1]
  have hVC (z : E × ℝ) (hz : z ∈ U ×ˢ (univ : Set ℝ)) : C z.1 ⬝ᵥ V z = 0 := by
    have hf := hframe z.1 hz.1
    simp [V, direction, dotProduct_add, dotProduct_smul, hf.2.2.2.2.1, hf.2.2.2.2.2.2]
  have hV0 (z : E × ℝ) (hz : z ∈ U ×ˢ (univ : Set ℝ)) : V z ≠ 0 := by
    apply smul_ne_zero (hR0 z.1 hz.1)
    have hf := hframe z.1 hz.1
    intro he
    have hu := direction_unit hf.1 hf.2.1 hf.2.2.1 z.2
    rw [he] at hu
    norm_num at hu
  have hN := leadingNormal_smoothOn (hU.prod isOpen_univ)
    (hX.comp contDiffOn_fst (fun z hz => hz.1))
    (hY.comp contDiffOn_fst (fun z hz => hz.1))
    (hC.comp contDiffOn_fst (fun z hz => hz.1)) hV
    (fun z hz => hD z.1 hz.1) hVY hVC hV0
  have hN0 (z : E × ℝ) (hz : z ∈ U ×ˢ (univ : Set ℝ)) :
      leadingNormal (X z.1) (Y z.1) (C z.1) (V z) ≠ 0 :=
    (leading_normal_nondegenerate (hD z.1 hz.1) (hVY z hz) (hVC z hz) (hV0 z hz)).2
  constructor
  · intro z hz
    exact (normalize_smoothAt (hN.contDiffAt ((hU.prod isOpen_univ).mem_nhds hz))
      (hN0 z hz)).contDiffWithinAt
  · exact (dot_smoothOn hN hN).sqrt (fun z hz => (dot_self_pos (hN0 z hz)).ne')

theorem frozen_coefficients_smoothOn {Q X Y C e₁ e₂ : E → Vec} {R : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hQ : ContDiffOn ℝ ∞ Q U) (hX : ContDiffOn ℝ ∞ X U)
    (hY : ContDiffOn ℝ ∞ Y U) (hC : ContDiffOn ℝ ∞ C U) (hR : ContDiffOn ℝ ∞ R U)
    (h₁ : ContDiffOn ℝ ∞ e₁ U) (h₂ : ContDiffOn ℝ ∞ e₂ U)
    (hD : ∀ x ∈ U, gramDet (Y x) (C x) ≠ 0)
    (hframe : ∀ x ∈ U, e₁ x ⬝ᵥ e₁ x = 1 ∧ e₂ x ⬝ᵥ e₂ x = 1 ∧ e₁ x ⬝ᵥ e₂ x = 0 ∧
      Y x ⬝ᵥ e₁ x = 0 ∧ C x ⬝ᵥ e₁ x = 0 ∧ Y x ⬝ᵥ e₂ x = 0 ∧ C x ⬝ᵥ e₂ x = 0)
    (hR0 : ∀ x ∈ U, R x ≠ 0) (d : E) :
    ContDiffOn ℝ ∞ (frozenFirst Q X Y C R e₁ e₂ d) (U ×ˢ univ) ∧
      ContDiffOn ℝ ∞ (frozenSize X Y C R e₁ e₂) (U ×ˢ univ) := by
  obtain ⟨hN, hS⟩ := frozen_normals_smoothOn hU hX hY hC hR h₁ h₂ hD hframe hR0
  exact ⟨dot_smoothOn (frozenError_smoothOn hU hQ hR h₁ h₂ d) hN, hS⟩

theorem actual_first_eq_frozen {Q X Y C e₁ e₂ : E → Vec} {R α : E → ℝ} {x d : E}
    (hQ : DifferentiableAt ℝ Q x) (hR : DifferentiableAt ℝ R x)
    (h₁ : DifferentiableAt ℝ e₁ x) (h₂ : DifferentiableAt ℝ e₂ x)
    (hα : DifferentiableAt ℝ α x)
    (hframe : e₁ x ⬝ᵥ e₁ x = 1 ∧ e₂ x ⬝ᵥ e₂ x = 1 ∧ e₁ x ⬝ᵥ e₂ x = 0 ∧
      Y x ⬝ᵥ e₁ x = 0 ∧ C x ⬝ᵥ e₁ x = 0 ∧ Y x ⬝ᵥ e₂ x = 0 ∧ C x ⬝ᵥ e₂ x = 0) :
    fderiv ℝ (fun y => Q y + R y • direction (e₁ y) (e₂ y) (α y)) x d ⬝ᵥ
        frozenNormal X Y C R e₁ e₂ (x, α x) =
      frozenFirst Q X Y C R e₁ e₂ d (x, α x) := by
  rw [circular_velocity_derivative hQ hR h₁ h₂ hα]
  exact first_normal_derivative_independent
    (angularDirection_normal_perp (R x) (α x) hframe.1 hframe.2.1 hframe.2.2.1
      hframe.2.2.2.1 hframe.2.2.2.2.2.1 hframe.2.2.2.2.1 hframe.2.2.2.2.2.2) _ _

end ClosedSurfaceR4.VelocityFrame

end

end OAI
