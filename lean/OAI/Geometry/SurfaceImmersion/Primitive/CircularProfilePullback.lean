import OAI.Geometry.SurfaceImmersion.Primitive.CircularJetProfiles

namespace OAI

/-! Pull back the circular profiles through the actual second-jet section.
The only derivative of the section that enters is its transverse derivative. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open NormalFrame VelocityFrame RealModes
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem circularFamilyProfile_comp {φ : E → F} {Q X Y C e₁ e₂ : F → Vec}
    {R : F → ℝ} {α : F × ℝ → ℝ} {x : E} {t : ℝ}
    (hφ : DifferentiableAt ℝ φ x) (hQ : DifferentiableAt ℝ Q (φ x))
    (hR : DifferentiableAt ℝ R (φ x)) (h₁ : DifferentiableAt ℝ e₁ (φ x))
    (h₂ : DifferentiableAt ℝ e₂ (φ x)) (hα : DifferentiableAt ℝ α (φ x,t)) (d : E) :
    circularFamilyProfile (Q ∘ φ) (X ∘ φ) (Y ∘ φ) (C ∘ φ) (R ∘ φ)
      (e₁ ∘ φ) (e₂ ∘ φ) (fun z => α (φ z.1,z.2)) d (x,t) =
    circularFamilyProfile Q X Y C R e₁ e₂ α (fderiv ℝ φ x d) (φ x,t) := by
  have hσ := (hφ.hasFDerivAt.comp (x,t)
    (hasFDerivAt_fst (𝕜 := ℝ) (p := (x,t)))).prodMk
    (hasFDerivAt_snd (𝕜 := ℝ) (p := (x,t)))
  have hβ : fderiv ℝ (fun z : E × ℝ => α (φ z.1,z.2)) (x,t) (0,1) =
      fderiv ℝ α (φ x,t) (0,1) := by
    simpa [Function.comp_def,ContinuousLinearMap.comp_apply,ContinuousLinearMap.fst,
      ContinuousLinearMap.snd] using
      congrArg (fun L : (E × ℝ) →L[ℝ] ℝ => L (0,1)) (hα.hasFDerivAt.comp (x,t) hσ).fderiv
  have hf := hasFDerivAt_fst (𝕜 := ℝ) (p := (φ x,t))
  have hV := (hQ.hasFDerivAt.comp (φ x,t) hf).add ((hR.hasFDerivAt.comp (φ x,t) hf).smul
    ((hα.hasFDerivAt.cos.smul (h₁.hasFDerivAt.comp (φ x,t) hf)).add
      (hα.hasFDerivAt.sin.smul (h₂.hasFDerivAt.comp (φ x,t) hf))))
  change HasFDerivAt (fun z : F × ℝ => Q z.1+
    R z.1 • direction (e₁ z.1) (e₂ z.1) (α z)) _ (φ x,t) at hV
  have hW :
      fderiv ℝ (fun z : E × ℝ => Q (φ z.1)+
        R (φ z.1) • direction (e₁ (φ z.1)) (e₂ (φ z.1)) (α (φ z.1,z.2))) (x,t) (d,0) =
      fderiv ℝ (fun z : F × ℝ => Q z.1+
        R z.1 • direction (e₁ z.1) (e₂ z.1) (α z)) (φ x,t) (fderiv ℝ φ x d,0) := by
    simpa [Function.comp_def,ContinuousLinearMap.comp_apply,ContinuousLinearMap.fst,
      ContinuousLinearMap.snd] using
      congrArg (fun L : (E × ℝ) →L[ℝ] Vec => L (d,0)) (hV.differentiableAt.hasFDerivAt.comp (x,t) hσ).fderiv
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact hW
  · change ((R ∘ φ) x * fderiv ℝ (fun z => α (φ z.1,z.2)) (x,t) (0,1)) • _ = _
    rw [hβ]
    rfl

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
