import OAI.GroupTheory.PolycyclicRecognition.Geometry.LieHomDifferential

namespace OAI

/-! # The actual differential of conjugation

This constructs the adjoint action on the tangent space from the manifold
derivative and proves its compatibility with the intrinsic exponential.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]

/-- Differential at the identity, with the codomain identified using the
homomorphism's identity law. -/
def identityDifferential (φ : G →* G) :
    GroupLieAlgebra (𝓘(ℝ, E)) G →L[ℝ] GroupLieAlgebra (𝓘(ℝ, E)) G :=
  mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ 1

omit [LieGroup (𝓘(ℝ, E)) ⊤ G] in
theorem identityDifferential_comp (φ ψ : G →* G)
    (hφ : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ 1)
    (hψ : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) ψ 1) :
    identityDifferential (E := E) (φ.comp ψ) =
      (identityDifferential (E := E) φ).comp (identityDifferential (E := E) ψ) := by
  have hφ' : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ (ψ 1) := by
    rw [map_one]
    exact hφ
  have hc := mfderiv_comp (I' := 𝓘(ℝ, E)) 1 hφ' hψ
  have hp : (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ (ψ 1) : E →L[ℝ] E) =
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ 1 : E →L[ℝ] E) := by
    congr 1
    exact ψ.map_one
  rw [hp] at hc
  exact hc

omit [LieGroup (𝓘(ℝ, E)) ⊤ G] in
@[simp] theorem identityDifferential_id :
    identityDifferential (E := E) (MonoidHom.id G) = ContinuousLinearMap.id ℝ _ := by
  change mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) id 1 = _
  rw [mfderiv_id]

theorem contMDiff_conjugation (g : G) :
    ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) ⊤ ((MulAut.conj g).toMonoidHom) := by
  have hl : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) ⊤ (fun x : G => g * x) :=
    contMDiff_mul_left
  have hr : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) ⊤ (fun x : G => x * g⁻¹) :=
    contMDiff_mul_right
  exact hr.comp hl

/-- The adjoint action as a monoid homomorphism into continuous linear
endomorphisms of the actual tangent Lie algebra. -/
def conjugationDifferentialHom :
    G →* (GroupLieAlgebra (𝓘(ℝ, E)) G →L[ℝ] GroupLieAlgebra (𝓘(ℝ, E)) G) where
  toFun g := identityDifferential ((MulAut.conj g).toMonoidHom)
  map_one' := by
    have h : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
      ext x
      simp
    rw [h, identityDifferential_id]
    rfl
  map_mul' g h := by
    have heq : (MulAut.conj (g * h)).toMonoidHom =
        ((MulAut.conj g).toMonoidHom).comp ((MulAut.conj h).toMonoidHom) := by
      ext x
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
        MonoidHom.comp_apply, MulAut.conj_apply, mul_inv_rev, mul_assoc]
    rw [heq, identityDifferential_comp _ _
      ((contMDiff_conjugation g).mdifferentiableAt (by simp))
      ((contMDiff_conjugation h).mdifferentiableAt (by simp))]
    rfl

theorem conjugation_exponential [T2Space G]
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (g : G) (v : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    g * Exp v * g⁻¹ = Exp (conjugationDifferentialHom g v) :=
  hExp.map_of_mdifferentiable hExp (MulAut.conj g).toMonoidHom
    ((contMDiff_conjugation g).mdifferentiable (by simp)) v

end PolycyclicRecognition

end

end OAI
