import OAI.Geometry.SurfaceImmersion.Geometry.C1ImmersionJets

namespace OAI

/-! A sufficiently small supported C1 change in a compact regular set
preserves the exact singular set of the original map. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem supported_regular_change {f : Base → V}
    (hf : ContDiff ℝ ∞ f) {K : Set Base} (hK : IsCompact K)
    (hI : ∀ x ∈ K, Function.Injective (fderiv ℝ f x)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q : Base → V, ContDiff ℝ ∞ q →
      tsupport q ⊆ K → (∀ x, ‖fderiv ℝ q x‖ < ε) →
      ∀ x, Function.Injective (fderiv ℝ (f+q) x) ↔ Function.Injective (fderiv ℝ f x) := by
  have hD : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  obtain ⟨ε,hε,hstable⟩ := compact_injective_stability (hK.image hD)
    (by rintro L ⟨x,hx,rfl⟩; exact hI x hx)
  refine ⟨ε,hε,?_⟩
  intro q hq hs hb x
  by_cases hx : x ∈ K
  · have hnew : Function.Injective (fderiv ℝ (f+q) x) := by
      apply hstable (fderiv ℝ f x) ⟨x,hx,rfl⟩
      rw [fderiv_add (hf.differentiable (by simp) x) (hq.differentiable (by simp) x),
        add_sub_cancel_left]
      exact hb x
    exact ⟨fun _ => hI x hx,fun _ => hnew⟩
  · have hn : x ∉ tsupport q := fun hxq => hx (hs hxq)
    have he : f+q =ᶠ[𝓝 x] f := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hn] with y hy
      simp [hy]
    rw [he.fderiv_eq]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
