import OAI.Geometry.SurfaceImmersion.Whitney.SmoothDoubleAtlas

namespace OAI

/-! The transition functions of the actual smooth double-locus charts
have smooth local inverses and nonzero derivative. -/
noncomputable section
open Set Filter Manifold Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothDoubleChart
variable {f : M → ProjectionTarget 3}

omit [IsManifold planeModel ∞ M] in
lemma transition_mem_overlap (a b : SmoothDoubleChart f) {t : ℝ} (ht : t ∈ a.overlap b) :
    a.transition b t ∈ b.overlap a := by
  refine ⟨a.coord.map_source ht.2,?_⟩
  change a.coord.symm (a.coord (b.coord.symm t)) ∈ b.coord.source
  rw [a.coord.left_inv ht.2]
  exact b.coord.map_target ht.1

omit [IsManifold planeModel ∞ M] in
lemma transition_inverse (a b : SmoothDoubleChart f) {t : ℝ} (ht : t ∈ a.overlap b) :
    b.transition a (a.transition b t) = t := by
  change b.coord (a.coord.symm (a.coord (b.coord.symm t))) = t
  rw [a.coord.left_inv ht.2,b.coord.right_inv ht.1]

theorem transition_derivative_product (a b : SmoothDoubleChart f) {t : ℝ}
    (ht : t ∈ a.overlap b) :
    deriv (b.transition a) (a.transition b t) * deriv (a.transition b) t = 1 := by
  have hF : DifferentiableAt ℝ (a.transition b) t :=
    ((a.transition_smooth b).contDiffAt ((a.overlap_open b).mem_nhds ht)).differentiableAt (by simp)
  have hG : DifferentiableAt ℝ (b.transition a) (a.transition b t) :=
    ((b.transition_smooth a).contDiffAt ((b.overlap_open a).mem_nhds
      (a.transition_mem_overlap b ht))).differentiableAt (by simp)
  have he : (b.transition a) ∘ (a.transition b) =ᶠ[𝓝 t] id := by
    filter_upwards [(a.overlap_open b).mem_nhds ht] with s hs
    exact a.transition_inverse b hs
  have hd := deriv_comp t hG hF
  rw [he.deriv_eq,deriv_id] at hd
  exact hd.symm

lemma transition_derivative_ne_zero (a b : SmoothDoubleChart f) {t : ℝ}
    (ht : t ∈ a.overlap b) : deriv (a.transition b) t ≠ 0 := by
  intro hz
  have h := a.transition_derivative_product b ht
  rw [hz,mul_zero] at h
  norm_num at h

end SmoothDoubleChart
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
