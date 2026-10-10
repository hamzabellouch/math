import OAI.Geometry.Cannon.Beltrami.TwoPointNormalize

namespace OAI

/-! Strong L2 stability of the actual principal density under uniformly
bounded almost-everywhere coefficient approximation. -/
open MeasureTheory Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

lemma schwartz_principal_density_equation (μ h : SchwartzMap ℂ ℂ)
    {k : ℝ} (hk : 0 ≤ k) (hb : ∀ z, ‖μ z‖ ≤ k)
    (he : ∀ z, h z-μ z*smoothBeurling h z=μ z) :
    h.toLp 2 (μ:=volume)-multiplier μ μ.continuous.aestronglyMeasurable hk
      (.of_forall hb) (beurling (h.toLp 2 (μ:=volume)))=μ.toLp 2 (μ:=volume) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (h.toLp 2 (μ:=volume))
    (multiplier μ μ.continuous.aestronglyMeasurable hk (.of_forall hb)
      (beurling (h.toLp 2 (μ:=volume)))),
    multiplier_ae μ μ.continuous.aestronglyMeasurable hk (.of_forall hb)
      (beurling (h.toLp 2 (μ:=volume))),
    h.coeFn_toLp 2 volume, μ.coeFn_toLp 2 volume,
    (schwartz_smoothL2 h).beurling.representative_ae] with z h1 h2 h3 h4 h5
  simp only [Pi.sub_apply] at h1
  rw [h1,h2,h3,h4,h5]
  exact he z

lemma principal_density_strong_convergence
    (μ : ℂ → ℂ) (ν : ℕ → ℂ → ℂ)
    (hm : AEStronglyMeasurable μ volume)
    (hn : ∀ n, AEStronglyMeasurable (ν n) volume)
    {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1)
    (hb : ∀ᵐ z ∂volume, ‖μ z‖ ≤ k)
    (hc : ∀ n, ∀ᵐ z ∂volume, ‖ν n z‖ ≤ k)
    (ht : ∀ᵐ z ∂volume, Tendsto (fun n => ν n z) atTop (𝓝 (μ z)))
    (g b : PlaneL2) (gₙ bₙ : ℕ → PlaneL2)
    (he : g-multiplier μ hm hk hb (beurling g)=b)
    (heₙ : ∀ n, gₙ n-multiplier (ν n) (hn n) hk (hc n) (beurling (gₙ n))=bₙ n)
    (hlim : Tendsto bₙ atTop (𝓝 b)) : Tendsto gₙ atTop (𝓝 g) := by
  have hmul := multiplier_strong_convergence_filter ν μ hn hm hk hc hb ht (beurling g)
  have hbn := (tendsto_iff_norm_sub_tendsto_zero.mp hlim)
  have hmn := (tendsto_iff_norm_sub_tendsto_zero.mp hmul)
  have hmajor := (hbn.add hmn).div_const (1-k)
  simp only [zero_add, zero_div] at hmajor
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hmajor
  exact beltrami_solution_difference μ (ν n) hm (hn n) hk hk1 hb (hc n)
    g (gₙ n) b (bₙ n) he (heₙ n)

end CircleDomainRigidity

end

end OAI
