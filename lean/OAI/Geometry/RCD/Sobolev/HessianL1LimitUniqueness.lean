import OAI.Geometry.RCD.Metric.L1SequentialLimit

namespace OAI

/-! # Uniqueness of local Hessian limits under vanishing L1 differences -/

open Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem L1_tendsto_of_integral_abs (F : ℕ → X → ℝ)
    (hF : ∀ k, Integrable (F k) μ) (J : Lp ℝ 1 μ)
    (hJ : Tendsto (fun k => ∫ x, |F k x-J x| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => (hF k).toL1 (F k)) atTop (𝓝 J) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply hJ.congr'
  exact Eventually.of_forall fun k => by
    change (∫ x, |F k x-J x| ∂μ) = dist ((hF k).toL1 (F k)) J
    rw [L1.dist_eq_integral_dist]
    apply integral_congr_ae
    filter_upwards [(hF k).coeFn_toL1] with x hx
    rw [hx,Real.dist_eq]

theorem L1_limits_eq_of_difference (F G : ℕ → X → ℝ)
    (hF : ∀ k, Integrable (F k) μ) (hG : ∀ k, Integrable (G k) μ)
    (I J : Lp ℝ 1 μ)
    (hI : Tendsto (fun k => ∫ x, |F k x-I x| ∂μ) atTop (𝓝 0))
    (hJ : Tendsto (fun k => ∫ x, |G k x-J x| ∂μ) atTop (𝓝 0))
    (hdiff : Tendsto (fun k => ∫ x, |F k x-G k x| ∂μ) atTop (𝓝 0)) : I=J := by
  have hlim := (L1_tendsto_of_integral_abs μ F hF I hI).dist
    (L1_tendsto_of_integral_abs μ G hG J hJ)
  have he (k : ℕ) : dist ((hF k).toL1 (F k)) ((hG k).toL1 (G k)) =
      ∫ x, |F k x-G k x| ∂μ := by
    rw [L1.dist_eq_integral_dist]
    apply integral_congr_ae
    filter_upwards [(hF k).coeFn_toL1,(hG k).coeFn_toL1] with x hx hy
    rw [hx,hy,Real.dist_eq]
  have hz : dist I J=0 := tendsto_nhds_unique hlim
    (hdiff.congr' (Eventually.of_forall fun k => (he k).symm))
  exact dist_eq_zero.mp hz

theorem L1_limit_eq_of_convergence (F : ℕ → X → ℝ)
    (hF : ∀ k, Integrable (F k) μ) (J : Lp ℝ 1 μ)
    (hJ : Tendsto (fun k => ∫ x, |F k x-J x| ∂μ) atTop (𝓝 0))
    (g : X → ℝ) (hg : Integrable g μ)
    (hlim : Tendsto (fun k => ∫ x, |F k x-g x| ∂μ) atTop (𝓝 0)) :
    J =ᵐ[μ] g := by
  have he (k : ℕ) : (∫ x, |F k x-(hg.toL1 g) x| ∂μ)=∫ x, |F k x-g x| ∂μ := by
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toL1] with x hx
    rw [hx]
  have hl := L1_tendsto_of_integral_abs μ F hF (hg.toL1 g)
    (hlim.congr' (Eventually.of_forall fun k => (he k).symm))
  have hEq : J=hg.toL1 g := tendsto_nhds_unique (L1_tendsto_of_integral_abs μ F hF J hJ) hl
  rw [hEq]
  exact hg.coeFn_toL1

end RegularPointCoordinates

end

end OAI
