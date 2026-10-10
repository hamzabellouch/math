import OAI.Geometry.SurfaceImmersion.Geometry.GraphBlendBounds

namespace OAI

/-! All convex interpolations between two graphs remain in a prescribed
neighborhood when their common base point is approached. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def graphPoint (f : ℝ → ℝ) (x : ℝ) : Base := ![x,f x]

lemma graphPoint_continuous {f : ℝ → ℝ} (hf : Continuous f) : Continuous (graphPoint f) := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_id
  · exact hf

lemma roundedReturnCurve_eq_blend (f g : ℝ → ℝ) (a b t : ℝ) :
    roundedReturnCurve f g a b t =
      (1-centeredSmoothStep t) • graphPoint f (a+b*t^2) +
        centeredSmoothStep t • graphPoint g (a+b*t^2) := by
  ext i
  fin_cases i
  · change a+b*t^2 = (1-centeredSmoothStep t)*(a+b*t^2)+centeredSmoothStep t*(a+b*t^2)
    ring
  · rfl

theorem small_graph_blends {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (x : ℝ) (he : f x = g x) {V : Set Base} (hV : IsOpen V)
    (hx : graphPoint f x ∈ V) :
    ∃ δ > 0, ∀ y ∈ Ioo (x-δ) (x+δ), ∀ s ∈ Icc (0:ℝ) 1,
      (1-s) • graphPoint f y + s • graphPoint g y ∈ V := by
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hV _ hx
  have hcenter : graphPoint f x = graphPoint g x := by simp [graphPoint,he]
  have hF : ∀ᶠ y in 𝓝 x, graphPoint f y ∈ Metric.ball (graphPoint f x) ε :=
    (graphPoint_continuous hf).continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hε)
  have hG : ∀ᶠ y in 𝓝 x, graphPoint g y ∈ Metric.ball (graphPoint f x) ε := by
    rw [hcenter]
    exact (graphPoint_continuous hg).continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hε)
  obtain ⟨δ,hδ,hsmall⟩ := Metric.eventually_nhds_iff.mp (hF.and hG)
  refine ⟨δ,hδ,?_⟩
  intro y hy s hs
  have hyd : dist y x < δ := by rw [Real.dist_eq]; exact abs_lt.mpr ⟨by linarith [hy.1],by linarith [hy.2]⟩
  obtain ⟨hfy,hgy⟩ := hsmall hyd
  apply hball
  exact (convex_ball (graphPoint f x) ε) hfy hgy (sub_nonneg.mpr hs.2) hs.1 (by ring)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
