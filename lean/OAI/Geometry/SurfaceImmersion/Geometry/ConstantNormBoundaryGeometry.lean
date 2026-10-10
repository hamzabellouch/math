import OAI.Geometry.SurfaceImmersion.Atlas.SphericalMetricPhaseData
import OAI.Geometry.SurfaceImmersion.Geometry.RealMetricDerivatives
import OAI.Geometry.SurfaceImmersion.Geometry.NormalInterpolation
import OAI.Geometry.SurfaceImmersion.Primitive.VelocityCoordinateData

namespace OAI

/-! The initial inward normal has a strictly positive pairing with every
nonzero directional second form, at every point of a constant-radius sphere. -/
noncomputable section
open Set Filter
open scoped ContDiff Matrix Topology
namespace ClosedSurfaceR4.RealModes
open SmallModes NormalFrame VelocityFrame

lemma constant_norm_radial_first {F : RField 4} {R : ℝ} {x : Base}
    (hF : DifferentiableAt ℝ F x) (hR : ∀ y, F y ⬝ᵥ F y = R) (v : Base) :
    F x ⬝ᵥ coordDeriv v F x = 0 := by
  have he : (fun y => F y ⬝ᵥ F y) = fun _ => R := funext hR
  have hd : coordDeriv v (fun y => F y ⬝ᵥ F y) x = 0 := by
    rw [he]
    simp [coordDeriv]
  rw [real_partial_dot hF hF,dotProduct_comm (coordDeriv v F x) (F x)] at hd
  linarith

lemma constant_norm_radial_second {F : RField 4} {U : Set Base} {R : ℝ}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (hR : ∀ y, F y ⬝ᵥ F y = R)
    {x : Base} (hx : x ∈ U) (v w : Base) :
    F x ⬝ᵥ coordDeriv v (coordDeriv w F) x =
      -(coordDeriv v F x ⬝ᵥ coordDeriv w F x) := by
  have hFx := (hF x hx).contDiffAt (hU.mem_nhds hx)
  have he : (fun y => F y ⬝ᵥ coordDeriv w F y) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact constant_norm_radial_first
      (((hF y hy).contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)) hR w
  have hd : coordDeriv v (fun y => F y ⬝ᵥ coordDeriv w F y) x = 0 := by
    change fderiv ℝ _ x v = 0
    rw [he.fderiv_eq]
    simp
  rw [real_partial_dot (hFx.differentiableAt (by simp))
    ((contDiffAt_coordDeriv hFx w).differentiableAt (by simp))] at hd
  linarith

lemma constant_norm_secondForm_inward {F : RField 4} {U : Set Base} {R : ℝ}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (hR : ∀ y, F y ⬝ᵥ F y = R)
    {x : Base} (hx : x ∈ U) (v w : Base) :
    realSecondForm F v w x ⬝ᵥ (-F x) = coordDeriv v F x ⬝ᵥ coordDeriv w F x := by
  have hFx := ((hF x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hX : coordDeriv dx F x ⬝ᵥ (-F x) = 0 := by
    rw [dotProduct_neg,dotProduct_comm,constant_norm_radial_first hFx hR,neg_zero]
  have hY : coordDeriv dy F x ⬝ᵥ (-F x) = 0 := by
    rw [dotProduct_neg,dotProduct_comm,constant_norm_radial_first hFx hR,neg_zero]
  unfold realSecondForm realNormalPart
  simp only [sub_dotProduct,smul_dotProduct,smul_eq_mul,hX,hY,mul_zero,sub_zero]
  rw [dotProduct_neg,dotProduct_comm,constant_norm_radial_second hU hF hR hx,neg_neg]

lemma positive_pairing_excludes_antipode {X n : Vec} (hp : 0 < X ⬝ᵥ n) :
    X ≠ 0 ∧ normalize X ≠ -n := by
  have hn : X ≠ 0 := by
    intro hz
    rw [hz,zero_dotProduct] at hp
    exact lt_irrefl _ hp
  refine ⟨hn,?_⟩
  intro he
  have hs := dot_normalize_self hn
  rw [he,dotProduct_neg] at hs
  linarith [Real.sqrt_nonneg (X ⬝ᵥ X)]

theorem constant_norm_boundary_geometry {F : RField 4} {U : Set Base} {R r : ℝ}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (hR : ∀ y, F y ⬝ᵥ F y = R)
    (hr : 0 < r) {x : Base} (hx : x ∈ U)
    (hI : Function.Injective (fderiv ℝ F x)) {v : Base} (hv : v ≠ 0) :
    0 < realSecondForm F v v x ⬝ᵥ (r⁻¹ • (-F x)) ∧
    realSecondForm F v v x ≠ 0 ∧
    normalize (realSecondForm F v v x) ≠ -(r⁻¹ • (-F x)) := by
  have hd : coordDeriv v F x ≠ 0 := by
    intro hz
    exact hv (hI (by simpa only [coordDeriv,map_zero] using hz))
  have hp : 0 < realSecondForm F v v x ⬝ᵥ (r⁻¹ • (-F x)) := by
    rw [dotProduct_smul,constant_norm_secondForm_inward hU hF hR hx]
    exact mul_pos (inv_pos.mpr hr) (dot_self_pos hd)
  exact ⟨hp,positive_pairing_excludes_antipode hp⟩

end ClosedSurfaceR4.RealModes

end

end OAI
