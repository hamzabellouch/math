import OAI.MeasureTheory.Falconer.Fourier.SmoothMask

namespace OAI

/-! # Buffered masks retain their good-direction support under differentiation -/

namespace Falconer
open Set MeasureTheory
open scoped Topology

theorem capCutoffAmbient_tsupport_subset {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Sphere d)) (U : Set (Sphere d)) :
    tsupport (capCutoffAmbient δ hδ S U) ⊆
      ⋃ c ∈ cutoffCapCenters δ S U, Metric.closedBall (c : Space d) δ := by
  apply closure_minimal _ (isClosed_biUnion_finset (fun _ _ => Metric.isClosed_closedBall))
  intro x hx
  obtain ⟨c,hc,hn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
  apply mem_iUnion₂.mpr ⟨c,hc,?_⟩
  have hb : capBump δ hδ c x ≠ 0 := (mul_ne_zero_iff.mp hn).1
  have hm : x ∈ Metric.ball (c : Space d) δ := by
    change x ∈ Metric.ball (c : Space d) (capBump δ hδ c).rOut
    rw [← (capBump δ hδ c).support_eq]
    exact hb
  exact Metric.ball_subset_closedBall hm

theorem capCutoffAmbient_derivative_support {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Sphere d)) (U : Set (Sphere d)) (k : ℕ) (w : Sphere d)
    (hw : iteratedFDeriv ℝ k (capCutoffAmbient δ hδ S U) (w : Space d) ≠ 0) : w ∈ U := by
  classical
  have hs := capCutoffAmbient_tsupport_subset hδ S U
    (support_iteratedFDeriv_subset (𝕜 := ℝ) k hw)
  obtain ⟨c,hc,hcw⟩ := mem_iUnion₂.mp hs
  exact (Finset.mem_filter.mp hc).2 w (by simpa only [Metric.mem_closedBall,Subtype.dist_eq] using hcw)

end Falconer

end OAI
