import OAI.Geometry.SurfaceImmersion.Atlas.PlaneCommonCoordinate

namespace OAI

/-! Two regular plane curves admit actual smooth graph representatives in
one common linear coordinate system. No angle condition is required. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem common_curve_graphs {γ δ : ℝ → Base} (hγ : ContDiff ℝ ∞ γ)
    (hδ : ContDiff ℝ ∞ δ) {s t : ℝ} (hs : deriv γ s ≠ 0) (ht : deriv δ t ≠ 0) :
    ∃ (e : Base ≃L[ℝ] Base) (g h : ℝ → ℝ) (U V : Set ℝ),
      ContDiff ℝ ∞ g ∧ ContDiff ℝ ∞ h ∧ IsOpen U ∧ IsOpen V ∧ s ∈ U ∧ t ∈ V ∧
      (∀ u ∈ U, e (γ u) = ![(e (γ u)) 0,g ((e (γ u)) 0)]) ∧
      (∀ v ∈ V, e (δ v) = ![(e (δ v)) 0,h ((e (δ v)) 0)]) ∧
      deriv (fun u => (e (γ u)) 0) s ≠ 0 ∧ deriv (fun v => (e (δ v)) 0) t ≠ 0 := by
  obtain ⟨e,hes,het⟩ := exists_common_plane_coordinate hs ht
  have hγe : HasDerivAt (e ∘ γ) (e (deriv γ s)) s :=
    e.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt s (hγ.differentiable (by simp) s).hasDerivAt
  have hδe : HasDerivAt (e ∘ δ) (e (deriv δ t)) t :=
    e.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t (hδ.differentiable (by simp) t).hasDerivAt
  have hs0 : deriv (fun u => (e (γ u)) 0) s ≠ 0 := by
    have h := (hasDerivAt_pi.mp hγe 0).deriv
    dsimp only [Function.comp_apply] at h
    rw [h]
    exact hes
  have ht0 : deriv (fun v => (e (δ v)) 0) t ≠ 0 := by
    have h := (hasDerivAt_pi.mp hδe 0).deriv
    dsimp only [Function.comp_apply] at h
    rw [h]
    exact het
  obtain ⟨g,U,hg,hU,hsU,hγgraph⟩ := plane_curve_graph (e.contDiff.comp hγ) s hs0
  obtain ⟨h,V,hh,hV,htV,hδgraph⟩ := plane_curve_graph (e.contDiff.comp hδ) t ht0
  exact ⟨e,g,h,U,V,hg,hh,hU,hV,hsU,htV,hγgraph,hδgraph,hs0,ht0⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
