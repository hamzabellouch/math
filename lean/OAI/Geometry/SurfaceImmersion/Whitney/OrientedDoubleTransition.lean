import OAI.Geometry.SurfaceImmersion.Whitney.OrientedDoubleChartArc
import OAI.Geometry.SurfaceImmersion.Whitney.ArcJoinOrientation

namespace OAI

/-! Transitions between oriented double-curve parameters remain local
smooth diffeomorphisms after a global smooth reparameterization. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

lemma smooth_real_homeomorph_deriv_ne_zero (e : ℝ ≃ₜ ℝ)
    (hes : ContDiff ℝ ∞ e) (hei : ContDiff ℝ ∞ e.symm) (x : ℝ) : deriv e x ≠ 0 := by
  have heq : e.symm ∘ e = id := by funext x; exact e.symm_apply_apply x
  have hd := deriv_comp x ((hei.differentiable (by simp)) (e x)) ((hes.differentiable (by simp)) x)
  rw [heq,deriv_id] at hd
  intro hz
  rw [hz,mul_zero] at hd
  norm_num at hd

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothDoubleChart
variable {f : M → ProjectionTarget 3}

theorem reparameterized_transition (c d : SmoothDoubleChart f)
    {s t : ℝ} (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1)
    (e : ℝ ≃ₜ ℝ) (hes : ContDiff ℝ ∞ e) (hei : ContDiff ℝ ∞ e.symm)
    {x : ℝ} (hx : s*e x ∈ d.overlap c) :
    ∃ (U : Set ℝ) (h : ℝ → ℝ), IsOpen U ∧ x ∈ U ∧
      ContDiffOn ℝ ∞ h U ∧ deriv h x ≠ 0 ∧
      h x = t*d.coord (c.coord.symm (s*e x)) ∧
      (fun u => c.coord.symm (s*e u)) =ᶠ[𝓝 x] (fun u => d.coord.symm (t*h u)) := by
  let k : ℝ → ℝ := fun u => s*e u
  let U := k ⁻¹' d.overlap c
  let h : ℝ → ℝ := fun u => t*d.transition c (k u)
  have hk : ContDiff ℝ ∞ k := contDiff_const.mul hes
  have hU : IsOpen U := (d.overlap_open c).preimage hk.continuous
  have hxU : x ∈ U := hx
  have hhs : ContDiffOn ℝ ∞ h U := contDiffOn_const.mul
    ((d.transition_smooth c).comp hk.contDiffOn (fun _ hu => hu))
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  have ht0 : t ≠ 0 := by rcases ht with rfl | rfl <;> norm_num
  have htt : t*t = 1 := by rcases ht with rfl | rfl <;> norm_num
  have hcD := ((d.transition_smooth c).contDiffAt ((d.overlap_open c).mem_nhds hx)).differentiableAt (by simp)
  have hd := ((hcD.hasDerivAt.comp x (((hes.differentiable (by simp)) x).hasDerivAt.const_mul s)).const_mul t).deriv
  have hn : deriv h x ≠ 0 := by
    change deriv (fun u => t*d.transition c (s*e u)) x ≠ 0
    dsimp only [Function.comp_def] at hd
    rw [hd]
    exact mul_ne_zero ht0 (mul_ne_zero (d.transition_derivative_ne_zero c hx)
      (mul_ne_zero hs0 (smooth_real_homeomorph_deriv_ne_zero e hes hei x)))
  refine ⟨U,h,hU,hxU,hhs,hn,rfl,?_⟩
  filter_upwards [hU.mem_nhds hxU] with u hu
  change c.coord.symm (s*e u) = d.coord.symm (t*(t*d.coord (c.coord.symm (s*e u))))
  rw [← mul_assoc,htt,one_mul,d.coord.left_inv hu.2]

end SmoothDoubleChart
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
