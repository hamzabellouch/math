import OAI.Geometry.SurfaceImmersion.Geometry.LocalMonotoneTransition
import OAI.Geometry.SurfaceImmersion.Whitney.SmoothDoubleTransitions

namespace OAI

/-! Actual double-locus chart changes admit global oriented smooth
reparametrizations retaining both surface-sheet germs. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothDoubleChart
variable {f : M → ProjectionTarget 3}

theorem oriented_reparametrization (a b : SmoothDoubleChart f) {t : ℝ}
    (ht : t ∈ a.overlap b) :
    ∃ (s : ℝ) (e : ℝ ≃ₜ ℝ), (s = 1 ∨ s = -1) ∧
      ContDiff ℝ ∞ e ∧ ContDiff ℝ ∞ e.symm ∧ StrictMono e ∧
      (fun u => a.coord.symm (s * e u)) =ᶠ[𝓝 t] b.coord.symm := by
  have hn := a.transition_derivative_ne_zero b ht
  have hs : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      0 < deriv (fun u => s * a.transition b u) t := by
    by_cases hp : 0 < deriv (a.transition b) t
    · refine ⟨1,Or.inl rfl,?_⟩
      simpa only [one_mul] using hp
    · have hneg : deriv (a.transition b) t < 0 := lt_of_le_of_ne (le_of_not_gt hp) hn
      refine ⟨-1,Or.inr rfl,?_⟩
      simpa only [neg_one_mul,deriv.fun_neg] using neg_pos.mpr hneg
  obtain ⟨s,hs,hpos⟩ := hs
  have hss : s*s = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hsmooth : ContDiffOn ℝ ∞ (fun u => s * a.transition b u) (a.overlap b) :=
    contDiffOn_const.mul (a.transition_smooth b)
  obtain ⟨e,hes,hei,hem,he⟩ := local_increasing_diffeomorphism
    (a.overlap_open b) hsmooth ht hpos
  refine ⟨s,e,hs,hes,hei,hem,?_⟩
  filter_upwards [he,(a.overlap_open b).mem_nhds ht] with u hu hU
  rw [hu,← mul_assoc,hss,one_mul]
  exact a.coord.left_inv hU.2

end SmoothDoubleChart
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
