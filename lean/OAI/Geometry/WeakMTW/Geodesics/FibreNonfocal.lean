import Mathlib
import OAI.Geometry.WeakMTW.Geodesics.ExtendedMinimizers

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem exp_coordinates_smooth (b x : M) {v : TangentSpace (model n) b}
    (hv : exp b v ∈ (chartAt (Model n) x).source) :
    ContDiffAt ℝ ∞ (fun w => chartAt (Model n) x (exp b w)) v := by
  have hch := (contMDiffOn_extChartAt (I := model n) (n := ∞) (x := x) _ hv).contMDiffAt
    ((chartAt (Model n) x).open_source.mem_nhds hv)
  exact contMDiffAt_iff_contDiffAt.mp (hch.comp v (exp_fibre_smooth b v))

 theorem exp_coordinates_injective_derivative (b x : M) {v : TangentSpace (model n) b}
    (hv : v ∈ injectivityDomain b) (hx : exp b v ∈ (chartAt (Model n) x).source) :
    Function.Injective (fderiv ℝ (fun w => chartAt (Model n) x (exp b w)) v) := by
  rw [injective_iff_map_eq_zero]
  intro w hw
  apply radial_interior_no_focal_fan b v w hv x hx
  have hd : HasDerivAt (fun s : ℝ => v+s•w) w 0 := by
    convert! (hasDerivAt_const (0 : ℝ) v).add
      ((hasDerivAt_id (0 : ℝ)).smul_const w) using 1
    simp
  have hf := ((exp_coordinates_smooth b x hx).differentiableAt (by simp)).hasFDerivAt
  have hf' : HasFDerivAt (fun u => chartAt (Model n) x (exp b u))
      (fderiv ℝ (fun u => chartAt (Model n) x (exp b u)) v) (v+(0 : ℝ)•w) := by
    simpa only [zero_smul,add_zero] using hf
  have hh := hf'.comp_hasDerivAt (l := fun u => chartAt (Model n) x (exp b u)) (f := fun s : ℝ => v+s•w) 0 hd
  rw [hw] at hh
  exact hh

 theorem exp_coordinates_equiv_derivative (b x : M) {v : TangentSpace (model n) b}
    (hv : v ∈ injectivityDomain b) (hx : exp b v ∈ (chartAt (Model n) x).source) :
    ∃ D : TangentSpace (model n) b ≃L[ℝ] Model n,
      HasFDerivAt (fun w => chartAt (Model n) x (exp b w)) (D : TangentSpace (model n) b →L[ℝ] Model n) v := by
  let : FiniteDimensional ℝ (TangentSpace (model n) b) :=
    inferInstanceAs (FiniteDimensional ℝ (Model n))
  let A := fderiv ℝ (fun w => chartAt (Model n) x (exp b w)) v
  have hi := exp_coordinates_injective_derivative b x hv hx
  let e : TangentSpace (model n) b ≃ₗ[ℝ] Model n :=
    LinearEquiv.ofInjectiveEndo A.toLinearMap hi
  let D : TangentSpace (model n) b ≃L[ℝ] Model n := e.toContinuousLinearEquiv
  refine ⟨D,?_⟩
  exact ((exp_coordinates_smooth b x hx).differentiableAt (by simp)).hasFDerivAt

 theorem exp_coordinates_local_inverse (b x : M) {v : TangentSpace (model n) b}
    (hv : v ∈ injectivityDomain b) (hx : exp b v ∈ (chartAt (Model n) x).source) :
    ∃ e : OpenPartialHomeomorph (TangentSpace (model n) b) (Model n),
      (∀ w, e w = chartAt (Model n) x (exp b w)) ∧ v ∈ e.source ∧
      (∀ w ∈ e.source, exp b w ∈ (chartAt (Model n) x).source) ∧
      ContDiffOn ℝ ∞ e.symm e.target := by
  let : FiniteDimensional ℝ (TangentSpace (model n) b) :=
    inferInstanceAs (FiniteDimensional ℝ (Model n))
  let S : Set (TangentSpace (model n) b) := (exp (n := n) b) ⁻¹' (chartAt (Model n) x).source
  have hS : IsOpen S := (chartAt (Model n) x).open_source.preimage (exp_fibre_smooth b).continuous
  have hf : ContDiffOn ℝ ∞ (fun w => chartAt (Model n) x (exp b w)) S :=
    fun w hw => (exp_coordinates_smooth b x hw).contDiffWithinAt
  obtain ⟨D,hD⟩ := exp_coordinates_equiv_derivative b x hv hx
  obtain ⟨e,he,hev,hes,hei,_⟩ := NormalNeighborhood.exists_smooth_local_diffeomorph hS hf hx hD
  exact ⟨e,fun w => congrFun he w,hev,hes,hei⟩

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
