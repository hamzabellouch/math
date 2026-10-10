import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralDividedDifferenceEstimate

namespace OAI

/-! Joint convergence of derivatives controls spectral divided differences
even when both endpoints vary. -/

open Set Filter Topology Metric
namespace DefocusingNLS
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem spectral_divided_difference_tendsto
    (F F' : ℕ → ℂ → E) (U : Set ℂ) (hU : IsOpen U) (z : ℂ) (hz : z ∈ U) (D : E)
    (hF : ∀ᶠ n in atTop, ∀ w ∈ U, HasDerivAt (F n) (F' n w) w)
    (hD : Tendsto (fun p : ℕ × ℂ => F' p.1 p.2) (atTop ×ˢ 𝓝 z) (𝓝 D))
    (x y : ℕ → ℂ) (hx : Tendsto x atTop (𝓝 z)) (hy : Tendsto y atTop (𝓝 z))
    (hne : ∀ᶠ n in atTop, x n ≠ y n) :
    Tendsto (fun n => (x n-y n)⁻¹ • (F n (x n)-F n (y n))) atTop (𝓝 D) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hb : ∀ᶠ p : ℕ × ℂ in atTop ×ˢ 𝓝 z, ‖F' p.1 p.2-D‖ < ε/2 :=
    by simpa only [dist_eq_norm] using Metric.tendsto_nhds.mp hD (ε/2) (half_pos hε)
  obtain ⟨A,hA,B,hB,hAB⟩ := Filter.mem_prod_iff.mp hb
  obtain ⟨r,hr,hrB⟩ := Metric.mem_nhds_iff.mp (inter_mem hB (hU.mem_nhds hz))
  filter_upwards [hA,hF,hne,hx.eventually (ball_mem_nhds z hr),hy.eventually (ball_mem_nhds z hr)]
    with n hn hd hnxy hnx hny
  have hbound (w : ℂ) (hw : w ∈ ball z r) : ‖F' n w-D‖ ≤ ε/2 :=
    (hAB (show (n,w) ∈ A ×ˢ B from ⟨hn,(hrB hw).1⟩)).le
  have hest := spectral_divided_difference_estimate (F n) (F' n) D (ball z r)
    (convex_ball z r) (ε/2) (fun w hw => hd w (hrB hw).2) hbound (x n) (y n) hnx hny hnxy
  rw [dist_eq_norm]
  exact hest.trans_lt (half_lt_self hε)

end DefocusingNLS

end OAI
