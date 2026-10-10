import OAI.Geometry.SurfaceImmersion.Primitive.LeadingProfileMap
import OAI.Geometry.SurfaceImmersion.Primitive.CircularFamilyProfile

namespace OAI

/-! Identify the canonical boundary profiles with the actual circular loop
in the analytic second-jet coordinates. -/
noncomputable section
open Set Filter
open scoped ContDiff Matrix Topology
namespace ClosedSurfaceR4.GeometryPreservation
open NormalFrame VelocityFrame RealModes
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma circular_angular_derivative {R : E → ℝ} {e₁ e₂ : E → Vec}
    {α : E × ℝ → ℝ} {x : E} {t : ℝ}
    (hR : DifferentiableAt ℝ R x) (h₁ : DifferentiableAt ℝ e₁ x)
    (h₂ : DifferentiableAt ℝ e₂ x) (hα : DifferentiableAt ℝ α (x,t)) :
    fderiv ℝ (fun z : E × ℝ => R z.1 • direction (e₁ z.1) (e₂ z.1) (α z))
      (x,t) (0,1) = (R x*fderiv ℝ α (x,t) (0,1)) •
        angularDirection (e₁ x) (e₂ x) (α (x,t)) := by
  have hf := hasFDerivAt_fst (𝕜 := ℝ) (p := (x,t))
  have hd := (hR.hasFDerivAt.comp (x,t) hf).smul
    ((hα.hasFDerivAt.cos.smul (h₁.hasFDerivAt.comp (x,t) hf)).add
      (hα.hasFDerivAt.sin.smul (h₂.hasFDerivAt.comp (x,t) hf)))
  change HasFDerivAt (fun z : E × ℝ =>
    R z.1 • direction (e₁ z.1) (e₂ z.1) (α z)) _ (x,t) at hd
  rw [hd.fderiv]
  ext i
  simp [angularDirection,ContinuousLinearMap.comp_apply,ContinuousLinearMap.fst,
    Function.comp_def]
  ring

end GeometryPreservation

namespace SurfaceVelocityFamily.Loop
open NormalFrame VelocityFrame RealModes JetPolynomial JetVelocityCoordinates GeometryPreservation
variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

theorem circular_leadingProfileMap {R : LowJet → ℝ} {e₁ e₂ : LowJet → Vec}
    {α : LowJet × ℝ → ℝ} (hR : ContDiffOn ℝ ∞ R O)
    (h₁ : ContDiffOn ℝ ∞ e₁ O) (h₂ : ContDiffOn ℝ ∞ e₂ O)
    (hα : ContDiffOn ℝ ∞ α (O ×ˢ univ))
    (hvel : ∀ J ∈ O, ∀ t, l.velocity (J,t) =
      R J • direction (e₁ J) (e₂ J) (α (J,t)))
    {J : LowJet} (hJ : J ∈ O) (t : ℝ) (D : LowJet) :
    boundaryProfileMap (l.leadingProfileMap ((J,t),D)) =
      circularFamilyProfile tangent (slot 1) (slot 2) (slot 6) R e₁ e₂ α D (J,t) := by
  have hnb : (O : Set LowJet) ×ˢ (univ : Set ℝ) ∈ 𝓝 (J,t) :=
    (O.isOpen.prod isOpen_univ).mem_nhds ⟨hJ,mem_univ t⟩
  have hvgerm : l.velocity =ᶠ[𝓝 (J,t)]
      (fun z : LowJet × ℝ => R z.1 • direction (e₁ z.1) (e₂ z.1) (α z)) := by
    filter_upwards [hnb] with z hz
    exact hvel z.1 hz.1 z.2
  have hlgerm : l.leadingVelocity =ᶠ[𝓝 (J,t)]
      (fun z : LowJet × ℝ => tangent z.1+
        R z.1 • direction (e₁ z.1) (e₂ z.1) (α z)) := by
    filter_upwards [hvgerm] with z hz
    exact congrArg (fun v => tangent z.1+v) hz
  have hangle := circular_angular_derivative
    ((hR.contDiffAt (O.isOpen.mem_nhds hJ)).differentiableAt (by simp))
    ((h₁.contDiffAt (O.isOpen.mem_nhds hJ)).differentiableAt (by simp))
    ((h₂.contDiffAt (O.isOpen.mem_nhds hJ)).differentiableAt (by simp))
    ((hα.contDiffAt hnb).differentiableAt (by simp))
  funext i
  fin_cases i
  · change spaceCoordinates (JetVelocityCoordinates.toEuclidean (l.leadingVelocity (J,t))) = _
    rw [JetVelocityCoordinates.toEuclidean,ContinuousLinearEquiv.apply_symm_apply]
    exact hlgerm.eq_of_nhds
  · change spaceCoordinates (JetVelocityCoordinates.toEuclidean (slot 2 J)) = _
    exact spaceCoordinates.apply_symm_apply _
  · change spaceCoordinates (JetVelocityCoordinates.toEuclidean (slot 6 J)) = _
    exact spaceCoordinates.apply_symm_apply _
  · change spaceCoordinates (JetVelocityCoordinates.toEuclidean
      (fderiv ℝ l.leadingVelocity (J,t) (D,0))) = _
    rw [JetVelocityCoordinates.toEuclidean,ContinuousLinearEquiv.apply_symm_apply]
    exact congrArg (fun L : (LowJet × ℝ) →L[ℝ] Vec => L (D,0)) hlgerm.fderiv_eq
  · change spaceCoordinates (JetVelocityCoordinates.toEuclidean
      (fderiv ℝ l.velocity (J,t) (0,1))) = _
    rw [JetVelocityCoordinates.toEuclidean,ContinuousLinearEquiv.apply_symm_apply,hvgerm.fderiv_eq]
    exact hangle

end SurfaceVelocityFamily.Loop
end ClosedSurfaceR4

end

end OAI
