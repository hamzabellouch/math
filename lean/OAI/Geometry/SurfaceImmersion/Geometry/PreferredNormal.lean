import OAI.Geometry.Immersion.ClosedSurface.MetricModel

namespace OAI

/-! The global object carried by the primitive induction is a smooth unit
section of the normal bundle. A spherical starting immersion supplies one. -/
noncomputable section
open Manifold Filter
open scoped Topology
open scoped ContDiff
namespace ClosedSurfaceR4
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

structure PreferredNormal (F : M → Space) where
  vector : M → Space
  smooth : ContMDiff planeModel spaceModel ∞ vector
  unit : ∀ p, ‖vector p‖ = 1
  normal : ∀ p (v : TangentSpace planeModel p),
    inner ℝ (show Space from mfderiv planeModel spaceModel F p v) (vector p) = 0

lemma spherical_inward_normal {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hunit : ∀ p, ‖F p‖ = 1)
    (p : M) (v : TangentSpace planeModel p) :
    inner ℝ (show Space from mfderiv planeModel spaceModel F p v) (-F p) = 0 := by
  let q : Space → ℝ := fun y => inner ℝ y y
  have hq : ContDiff ℝ ∞ q := contDiff_id.inner ℝ contDiff_id
  have he : q ∘ F = fun _ => (1 : ℝ) := by
    funext x
    change inner ℝ (F x) (F x) = 1
    rw [real_inner_self_eq_norm_sq,hunit]
    norm_num
  have heq : q ∘ F =ᶠ[𝓝 p] (fun _ => (1 : ℝ)) := Filter.Eventually.of_forall (congrFun he)
  have hd := heq.mfderiv_eq (I := planeModel) (I' := 𝓘(ℝ))
  rw [mfderiv_comp p (hq.contMDiff.mdifferentiable (by simp)).mdifferentiableAt
    (hF.mdifferentiable (by simp)).mdifferentiableAt,mfderiv_eq_fderiv] at hd
  have hv := congrArg (fun L : TangentSpace planeModel p →L[ℝ] ℝ => L v) hd
  let w : Space := mfderiv planeModel spaceModel F p v
  simp only [mfderiv_const] at hv
  change fderiv ℝ q (F p) w = 0 at hv
  have hderiv : fderiv ℝ q (F p) w = 2 * inner ℝ w (F p) := by
    change fderiv ℝ (fun y : Space => inner ℝ y y) (F p) w = _
    rw [fderiv_inner_apply ℝ (f := fun y : Space => y) (g := fun y : Space => y)
      differentiableAt_id differentiableAt_id]
    simp only [fderiv_fun_id,ContinuousLinearMap.id_apply]
    change inner ℝ (F p) w + inner ℝ w (F p) = _
    rw [real_inner_comm (F p) w]
    ring
  change inner ℝ w (-F p) = 0
  rw [inner_neg_right]
  linarith

/-- The inward radial section is a global preferred normal, without an
orientation or a global choice of a second normal vector. -/
def sphericalPreferredNormal {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hunit : ∀ p, ‖F p‖ = 1) :
    PreferredNormal F where
  vector p := -F p
  smooth := hF.neg
  unit p := by simpa only [norm_neg] using hunit p
  normal := spherical_inward_normal hF hunit

end ClosedSurfaceR4

end

end OAI
