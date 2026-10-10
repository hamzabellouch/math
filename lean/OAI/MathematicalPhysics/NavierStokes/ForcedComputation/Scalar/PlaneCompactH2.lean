import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneCompactC1L2
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneSobolevL2

namespace OAI

/-! The prescribed compact drift has continuous spatial jets in L2.
These are the H2 conditions for its smooth spatial slices. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows PlanarHamiltonian MeasureTheory Set Filter
open scoped ContDiff Topology

theorem planeSpatialD_joint_smooth {F : ℝ → Plane → ℝ}
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (j : Fin 2) :
    ContDiff ℝ ∞ (Function.uncurry (fun t => spatialD j (F t))) := by
  have hc := (hF.fderiv_right (m := ∞) (by simp)).clm_apply
    (contDiff_const (c := ((0 : ℝ), basis j)))
  convert hc using 1
  funext y
  have hd := (hF.differentiable (by simp) y).hasFDerivAt.comp y.2
    ((hasFDerivAt_const (𝕜 := ℝ) y.1 y.2).prodMk (hasFDerivAt_id y.2))
  exact congrArg (fun L => L (basis j)) hd.fderiv

theorem planeSpatialD_zero_off_compact {F : ℝ → Plane → ℝ}
    {K : Set Plane} (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → F t x = 0) (j : Fin 2) (t : ℝ)
    {x : Plane} (hx : x ∉ K) : spatialD j (F t) x = 0 := by
  have he : F t =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
    exact hz t y hy
  unfold spatialD
  rw [he.fderiv_eq]
  simp only [fderiv_fun_const, Pi.zero_apply, zero_apply]

theorem compact_family_cInH2 {F : ℝ → Plane → ℝ}
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) {K : Set Plane} (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → F t x = 0) (T : ℝ) :
    PlaneCInH2 F (Icc 0 T) := by
  have hD (j : Fin 2) := planeSpatialD_joint_smooth hF j
  have hzD (j : Fin 2) : ∀ t x, x ∉ K → spatialD j (F t) x = 0 :=
    fun t _ hx => planeSpatialD_zero_off_compact hK hz j t hx
  refine ⟨compact_family_continuousL2 hF.continuous hK hz T, ?_, ?_⟩
  · intro j
    exact compact_family_continuousL2 (hD j).continuous hK (hzD j) T
  · intro j k
    exact compact_family_continuousL2 (planeSpatialD_joint_smooth (hD k) j).continuous
      hK (fun t _ hx => planeSpatialD_zero_off_compact hK (hzD k) j t hx) T

theorem PlaneContinuousL2.congr_slices {F G : ℝ → Plane → ℝ} {S : Set ℝ}
    (hF : PlaneContinuousL2 F S) (hFG : ∀ t ∈ S, F t = G t) : PlaneContinuousL2 G S := by
  obtain ⟨U, hU, hUF⟩ := hF
  refine ⟨U, hU, ?_⟩
  intro t ht
  rw [← hFG t ht]
  exact hUF t ht

theorem PlaneCInH2.congr_slices {F G : ℝ → Plane → ℝ} {S : Set ℝ}
    (hF : PlaneCInH2 F S) (hFG : ∀ t ∈ S, F t = G t) : PlaneCInH2 G S := by
  exact ⟨hF.1.congr_slices hFG,
    fun j => (hF.2.1 j).congr_slices (fun t ht => by rw [hFG t ht]),
    fun j k => (hF.2.2 j k).congr_slices (fun t ht => by rw [hFG t ht])⟩

theorem PlaneC1L2.congr_slices {F G F' G' : ℝ → Plane → ℝ} {S : Set ℝ}
    (hF : PlaneC1L2 F G S) (hFF : ∀ t ∈ S, F t = F' t)
    (hGG : ∀ t ∈ S, G t = G' t) : PlaneC1L2 F' G' S := by
  obtain ⟨U, V, hU, hV, hUV⟩ := hF
  refine ⟨U, V, hU, hV, ?_⟩
  intro t ht
  obtain ⟨hu, hv, hd⟩ := hUV t ht
  rw [hFF t ht] at hu
  rw [hGG t ht] at hv
  exact ⟨hu, hv, hd⟩

end ForcedComputation.VelocityDetector

end

end OAI
