import OAI.Geometry.SurfaceImmersion.Geometry.PreferredNormal
import OAI.Geometry.Immersion.ClosedSurface.ChartModel
import OAI.Geometry.SurfaceImmersion.Whitney.NormalCollarGluing
import OAI.Geometry.SurfaceImmersion.Geometry.ManifoldMetricCalculus

namespace OAI

/-! The collar construction produces the actual global preferred normal
carried by the finite primitive induction. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4
open RealModes VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

lemma coordinate_dot_self_of_unit {v : Space} (hv : ‖v‖ = 1) :
    spaceCoordinates v ⬝ᵥ spaceCoordinates v = 1 := by
  rw [spaceCoordinates_dot,real_inner_self_eq_norm_sq,hv]
  norm_num

lemma norm_coordinate_inverse_of_dot_self {v : NormalFrame.Vec} (hv : v ⬝ᵥ v = 1) :
    ‖spaceCoordinates.symm v‖ = 1 := by
  have he : ‖spaceCoordinates.symm v‖^2 = (1 : ℝ)^2 := by
    rw [← real_inner_self_eq_norm_sq,← spaceCoordinates_dot,
      ContinuousLinearEquiv.apply_symm_apply,hv,one_pow]
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp he

/-- Glue an interior normal to an exterior normal, retaining all positive
pairings needed on the later primitive boundaries. -/
theorem preferredNormal_collar {F a b : M → Space} {U V : Set M}
    (hU : IsOpen U) (hV : IsOpen V)
    (ha : ContMDiffOn planeModel spaceModel ∞ a U)
    (hb : ContMDiffOn planeModel spaceModel ∞ b V)
    (ha1 : ∀ p ∈ U, ‖a p‖ = 1) (hb1 : ∀ p ∈ V, ‖b p‖ = 1)
    (haN : ∀ p ∈ U, ∀ v : TangentSpace planeModel p,
      inner ℝ (surfaceDifferential F p v) (a p) = 0)
    (hbN : ∀ p ∈ V, ∀ v : TangentSpace planeModel p,
      inner ℝ (surfaceDifferential F p v) (b p) = 0)
    (hne : ∀ p ∈ U ∩ V, b p ≠ -a p)
    {chi : M → ℝ} (hchi : ContMDiff planeModel 𝓘(ℝ) ∞ chi)
    (hchiu : tsupport chi ⊆ U) (hchiv : tsupport (fun p => 1-chi p) ⊆ V)
    (hchi01 : ∀ p, chi p ∈ Icc (0 : ℝ) 1) :
    ∃ N : PreferredNormal F,
      (∀ p, chi p = 1 → N.vector p = a p) ∧
      (∀ p, chi p = 0 → N.vector p = b p) ∧
      (∀ p (w : Space), (p ∈ U → 0 < inner ℝ w (a p)) →
        (p ∈ V → 0 < inner ℝ w (b p)) → 0 < inner ℝ w (N.vector p)) := by
  let ac := spaceCoordinates ∘ a
  let bc := spaceCoordinates ∘ b
  have hac : ContMDiffOn planeModel 𝓘(ℝ,NormalFrame.Vec) ∞ ac U :=
    spaceCoordinates.contDiff.contMDiff.comp_contMDiffOn ha
  have hbc : ContMDiffOn planeModel 𝓘(ℝ,NormalFrame.Vec) ∞ bc V :=
    spaceCoordinates.contDiff.contMDiff.comp_contMDiffOn hb
  have hne' : ∀ p ∈ U ∩ V, bc p ≠ -ac p := by
    intro p hp hh
    apply hne p hp
    apply spaceCoordinates.injective
    simpa only [ac,bc,Function.comp_apply,map_neg] using hh
  obtain ⟨hsmooth,hunit,h1,h0,hperp,hpos⟩ := normal_collar_gluing hU hV hac hbc hchi hchiu hchiv
    hchi01 (fun p hp => coordinate_dot_self_of_unit (ha1 p hp))
    (fun p hp => coordinate_dot_self_of_unit (hb1 p hp)) hne'
  let n : M → Space := fun p => spaceCoordinates.symm (first (bc p) (ac p) (chi p))
  let hn : PreferredNormal F := {
    vector := n
    smooth := spaceCoordinates.symm.contDiff.contMDiff.comp hsmooth
    unit := fun p => norm_coordinate_inverse_of_dot_self (hunit p)
    normal := by
      intro p v
      change inner ℝ (surfaceDifferential F p v) (n p) = 0
      rw [← spaceCoordinates_dot]
      change spaceCoordinates (surfaceDifferential F p v) ⬝ᵥ first (bc p) (ac p) (chi p) = 0
      apply hperp
      · intro hp
        exact (spaceCoordinates_dot _ _).trans (haN p hp v)
      · intro hp
        exact (spaceCoordinates_dot _ _).trans (hbN p hp v)
  }
  refine ⟨hn,?_,?_,?_⟩
  · intro p hp
    change spaceCoordinates.symm (first (bc p) (ac p) (chi p)) = a p
    exact (congrArg spaceCoordinates.symm (h1 p hp)).trans
      (spaceCoordinates.symm_apply_apply (a p))
  · intro p hp
    change spaceCoordinates.symm (first (bc p) (ac p) (chi p)) = b p
    exact (congrArg spaceCoordinates.symm (h0 p hp)).trans
      (spaceCoordinates.symm_apply_apply (b p))
  · intro p w hwa hwb
    change inner ℝ w (n p) > 0
    rw [← spaceCoordinates_dot]
    change 0 < spaceCoordinates w ⬝ᵥ first (bc p) (ac p) (chi p)
    apply hpos
    · intro hp
      simpa only [ac,Function.comp_apply,spaceCoordinates_dot] using hwa hp
    · intro hp
      simpa only [bc,Function.comp_apply,spaceCoordinates_dot] using hwb hp

end ClosedSurfaceR4

end

end OAI
