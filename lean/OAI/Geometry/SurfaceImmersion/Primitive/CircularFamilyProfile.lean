import OAI.Geometry.SurfaceImmersion.Primitive.CircularProfileThreshold

namespace OAI

/-! The five boundary profiles for a smooth family of circular velocities. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open NormalFrame VelocityFrame RealModes
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def circularFamilyProfile (Q X Y C : E → Vec) (R : E → ℝ)
    (e₁ e₂ : E → Vec) (α : E × ℝ → ℝ) (d : E) (z : E × ℝ) : BoundaryProfile :=
  circularBoundaryProfile (X z.1) (Y z.1) (C z.1)
    (fderiv ℝ (fun w : E × ℝ => Q w.1 + R w.1 • direction (e₁ w.1) (e₂ w.1) (α w)) z (d,0))
    (e₁ z.1) (e₂ z.1) (R z.1) (α z) (fderiv ℝ α z (0,1))

lemma fderiv_slice_first {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E × ℝ → F} {x : E} {t : ℝ} (hf : DifferentiableAt ℝ f (x,t)) (d : E) :
    fderiv ℝ (fun y => f (y,t)) x d = fderiv ℝ f (x,t) (d,0) := by
  have hslice : HasFDerivAt (fun y : E => (y,t))
      ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] ℝ)) x :=
    (hasFDerivAt_id x).prodMk (hasFDerivAt_const t x)
  exact congrArg (fun L : E →L[ℝ] F => L d) (hf.hasFDerivAt.comp x hslice).fderiv

lemma circularFamilyProfile_spatial {Q X Y C e₁ e₂ : E → Vec} {R : E → ℝ}
    {α : E × ℝ → ℝ} {x : E} {t : ℝ}
    (hQ : DifferentiableAt ℝ Q x) (hR : DifferentiableAt ℝ R x)
    (h₁ : DifferentiableAt ℝ e₁ x) (h₂ : DifferentiableAt ℝ e₂ x)
    (hα : DifferentiableAt ℝ α (x,t)) (d : E) :
    circularFamilyProfile Q X Y C R e₁ e₂ α d (x,t) =
      circularSpatialProfile Q X Y C R e₁ e₂ (fun y => α (y,t))
        (fderiv ℝ α (x,t) (0,1)) x d := by
  have hf := hasFDerivAt_fst (𝕜 := ℝ) (p := (x,t))
  have hd := (hQ.hasFDerivAt.comp (x,t) hf).add ((hR.hasFDerivAt.comp (x,t) hf).smul
    ((hα.hasFDerivAt.cos.smul (h₁.hasFDerivAt.comp (x,t) hf)).add
      (hα.hasFDerivAt.sin.smul (h₂.hasFDerivAt.comp (x,t) hf))))
  change HasFDerivAt (fun w : E × ℝ =>
    Q w.1 + R w.1 • direction (e₁ w.1) (e₂ w.1) (α w)) _ (x,t) at hd
  unfold circularFamilyProfile circularSpatialProfile
  rw [fderiv_slice_first hd.differentiableAt]

lemma circularFamilyProfile_smoothOn {Q X Y C e₁ e₂ : E → Vec} {R : E → ℝ}
    {U : Set E} {α : E × ℝ → ℝ} (hU : IsOpen U)
    (hQ : ContDiffOn ℝ ∞ Q U) (hX : ContDiffOn ℝ ∞ X U)
    (hY : ContDiffOn ℝ ∞ Y U) (hC : ContDiffOn ℝ ∞ C U)
    (hR : ContDiffOn ℝ ∞ R U) (h₁ : ContDiffOn ℝ ∞ e₁ U) (h₂ : ContDiffOn ℝ ∞ e₂ U)
    (hα : ContDiffOn ℝ ∞ α (U ×ˢ univ))
    (hD : ∀ x ∈ U, gramDet (Y x) (C x) ≠ 0) (d : E) :
    ContDiffOn ℝ ∞ (circularFamilyProfile Q X Y C R e₁ e₂ α d) (U ×ˢ univ) := by
  have hX' : ContDiffOn ℝ ∞ (fun z : E × ℝ => X z.1) (U ×ˢ univ) := hX.comp contDiffOn_fst (fun z hz => hz.1)
  have hY' : ContDiffOn ℝ ∞ (fun z : E × ℝ => Y z.1) (U ×ˢ univ) := hY.comp contDiffOn_fst (fun z hz => hz.1)
  have hC' : ContDiffOn ℝ ∞ (fun z : E × ℝ => C z.1) (U ×ˢ univ) := hC.comp contDiffOn_fst (fun z hz => hz.1)
  have hR' : ContDiffOn ℝ ∞ (fun z : E × ℝ => R z.1) (U ×ˢ univ) := hR.comp contDiffOn_fst (fun z hz => hz.1)
  have h1' : ContDiffOn ℝ ∞ (fun z : E × ℝ => e₁ z.1) (U ×ˢ univ) := h₁.comp contDiffOn_fst (fun z hz => hz.1)
  have h2' : ContDiffOn ℝ ∞ (fun z : E × ℝ => e₂ z.1) (U ×ˢ univ) := h₂.comp contDiffOn_fst (fun z hz => hz.1)
  have hV : ContDiffOn ℝ ∞ (fun z : E × ℝ =>
      R z.1 • direction (e₁ z.1) (e₂ z.1) (α z)) (U ×ˢ univ) :=
    hR'.smul ((hα.cos.smul h1').add (hα.sin.smul h2'))
  have hW := ((hQ.comp contDiffOn_fst (fun z hz => hz.1)).add hV).fderiv_of_isOpen
    (hU.prod isOpen_univ) (m := ∞) (by simp)
  have hβ := hα.fderiv_of_isOpen (hU.prod isOpen_univ) (m := ∞) (by simp)
  have hn : ContDiffOn ℝ ∞ (fun z : E × ℝ => realNormalPart (Y z.1) (C z.1) (X z.1))
      (U ×ˢ univ) := by
    intro z hz
    exact (contDiffAt_realNormalPart
      (hY'.contDiffAt ((hU.prod isOpen_univ).mem_nhds hz))
      (hC'.contDiffAt ((hU.prod isOpen_univ).mem_nhds hz))
      (hX'.contDiffAt ((hU.prod isOpen_univ).mem_nhds hz)) (hD z.1 hz.1)).contDiffWithinAt
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i
  · exact (hX'.sub hn).add hV
  · exact hY'
  · exact hC'
  · exact hW.clm_apply contDiffOn_const
  · exact (hR'.mul (hβ.clm_apply contDiffOn_const)).smul
      (((hα.sin.neg).smul h1').add (hα.cos.smul h2'))

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
