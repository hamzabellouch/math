import Mathlib

namespace OAI

/-!
# The spherical lift of an ordinary surface immersion

Inverse stereographic projection lifts a smooth immersion into three-space
to a smooth spherical immersion in four-space, as in Section 8.1 of paper 094-01.
-/

noncomputable section

namespace ClosedSurfaceR4.SphericalStart

open Set Manifold
open scoped ContDiff Topology InnerProductSpace

abbrev Space := EuclideanSpace ℝ (Fin 4)
abbrev ThreeSpace := EuclideanSpace ℝ (Fin 3)
abbrev Hyperplane (v : Space) := (ℝ ∙ v)ᗮ

/-- Inverse stereographic projection, regarded as an ambient R4-valued map. -/
def lift (v : Space) (w : Hyperplane v) : Space := stereoInvFunAux v w

lemma lift_smooth (v : Space) : ContDiff ℝ ∞ (lift v) :=
  contDiff_stereoInvFunAux.comp (ℝ ∙ v)ᗮ.subtypeL.contDiff

lemma lift_norm {v : Space} (hv : ‖v‖ = 1) (w : Hyperplane v) :
    ‖lift v w‖ = 1 := by
  exact mem_sphere_zero_iff_norm.mp (stereoInvFunAux_mem hv w.property)

lemma lift_inner_lt_one {v : Space} (hv : ‖v‖ = 1) (w : Hyperplane v) :
    inner ℝ v (lift v w) < 1 := by
  apply (inner_lt_one_iff_real_of_norm_eq_one hv (lift_norm hv w)).mpr
  exact (Subtype.coe_ne_coe.mpr (stereoInvFun_ne_north_pole hv w)).symm

/-- Its differential is injective everywhere because stereographic projection
is a smooth left inverse on its image. -/
theorem lift_fderiv_injective {v : Space} (hv : ‖v‖ = 1) (w : Hyperplane v) :
    Function.Injective (fderiv ℝ (lift v) w) := by
  let U : Set Space := {x | inner ℝ v x ≠ 1}
  have hU : IsOpen U := isOpen_ne_fun (innerSL ℝ v).continuous continuous_const
  have hw : lift v w ∈ U := ne_of_lt (lift_inner_lt_one hv w)
  have hd : DifferentiableAt ℝ (stereoToFun v) (lift v w) := by
    exact ((contDiffOn_stereoToFun (v := v) (n := (1 : ℕ∞ω))).contDiffAt
      (hU.mem_nhds hw)).differentiableAt (by simp)
  have hl := (lift_smooth v).differentiable (by simp) w
  have he : stereoToFun v ∘ lift v = id := by
    funext z
    exact stereo_right_inv hv z
  have hchain : (fderiv ℝ (stereoToFun v) (lift v w)).comp
      (fderiv ℝ (lift v) w) = ContinuousLinearMap.id ℝ (Hyperplane v) := by
    rw [← fderiv_comp w hd hl, he, fderiv_id]
  intro a b hab
  have hab' := congrArg (fderiv ℝ (stereoToFun v) (lift v w)) hab
  change ((fderiv ℝ (stereoToFun v) (lift v w)).comp
    (fderiv ℝ (lift v) w)) a = ((fderiv ℝ (stereoToFun v) (lift v w)).comp
    (fderiv ℝ (lift v) w)) b at hab'
  simpa only [hchain, ContinuousLinearMap.id_apply] using hab'

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ M]

omit [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ M] in
/-- A smooth ordinary immersion into the three-dimensional hyperplane gives
an ambient smooth immersion with image in the unit three-sphere. -/
theorem spherical_immersion_of_hyperplane_immersion {v : Space} (hv : ‖v‖ = 1)
    {F : M → Hyperplane v}
    (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, Hyperplane v) ∞ F)
    (hI : ∀ p, Function.Injective
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, Hyperplane v) F p)) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, Space) ∞ (lift v ∘ F) ∧
      (∀ p, ‖lift v (F p)‖ = 1) ∧
      ∀ p, Function.Injective
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, Space) (lift v ∘ F) p) := by
  have hl := (lift_smooth v).contMDiff
  refine ⟨hl.comp hF, fun p => lift_norm hv (F p), ?_⟩
  intro p
  rw [mfderiv_comp p (hl.mdifferentiable (by simp)).mdifferentiableAt
    (hF.mdifferentiable (by simp)).mdifferentiableAt, mfderiv_eq_fderiv]
  exact (lift_fderiv_injective hv (F p)).comp (hI p)

/-- The hyperplane perpendicular to a nonzero vector in four-space is
isometrically three-dimensional. -/
def threeSpaceToHyperplane {v : Space} (hv : v ≠ 0) :
    ThreeSpace ≃ₗᵢ[ℝ] Hyperplane v := by
  letI : Fact (Module.finrank ℝ Space = 3 + 1) := ⟨by simp [Space]⟩
  exact (OrthonormalBasis.fromOrthogonalSpanSingleton 3 hv).repr.symm

omit [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ M] in
/-- The ordinary smooth three-space immersion supplied at the starting step
can be placed in the unit three-sphere. -/
theorem spherical_immersion_of_three_space_immersion {v : Space} (hv : ‖v‖ = 1)
    {F : M → ThreeSpace}
    (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, ThreeSpace) ∞ F)
    (hI : ∀ p, Function.Injective
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, ThreeSpace) F p)) :
    ∃ G : M → Space,
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, Space) ∞ G ∧
      (∀ p, ‖G p‖ = 1) ∧
      ∀ p, Function.Injective
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, Space) G p) := by
  have hv0 : v ≠ 0 := by
    intro he
    rw [he, norm_zero] at hv
    norm_num at hv
  let e := threeSpaceToHyperplane hv0
  have he : ContDiff ℝ ∞ e := e.toContinuousLinearEquiv.contDiff
  have hi : ∀ p, Function.Injective
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, Hyperplane v) (e ∘ F) p) := by
    intro p
    rw [mfderiv_comp p (he.contMDiff.mdifferentiable (by simp)).mdifferentiableAt
      (hF.mdifferentiable (by simp)).mdifferentiableAt, mfderiv_eq_fderiv]
    let D : EuclideanSpace ℝ (Fin 2) →L[ℝ] ThreeSpace :=
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, ThreeSpace) F p
    change Function.Injective ((fderiv ℝ e (F p)).comp D)
    have hde : fderiv ℝ e (F p) = e.toContinuousLinearEquiv.toContinuousLinearMap :=
      e.toContinuousLinearEquiv.hasFDerivAt.fderiv
    rw [hde]
    exact e.injective.comp (hI p)
  exact ⟨lift v ∘ (e ∘ F),
    spherical_immersion_of_hyperplane_immersion hv (he.contMDiff.comp hF) hi⟩

end ClosedSurfaceR4.SphericalStart

end

end OAI
