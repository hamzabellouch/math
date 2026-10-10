import OAI.Geometry.RCD.Sobolev.HessianL1MassBound

namespace OAI

/-! # Differences and density bounds pass through L1 approximation -/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem integral_abs_difference_tendsto_of_L1_error (F G : ℕ → X → ℝ)
    (hF : ∀ k, Integrable (F k) μ) (hG : ∀ k, Integrable (G k) μ)
    (I J : Lp ℝ 1 μ)
    (hI : Tendsto (fun k => ∫ x, |F k x-I x| ∂μ) atTop (𝓝 0))
    (hJ : Tendsto (fun k => ∫ x, |G k x-J x| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, |F k x-G k x| ∂μ) atTop
      (𝓝 (∫ x, |I x-J x| ∂μ)) := by
  have h := (L1_tendsto_of_integral_abs μ F hF I hI).dist
    (L1_tendsto_of_integral_abs μ G hG J hJ)
  have he (k : ℕ) : dist ((hF k).toL1 (F k)) ((hG k).toL1 (G k)) =
      ∫ x, |F k x-G k x| ∂μ := by
    rw [L1.dist_eq_integral_dist]
    apply integral_congr_ae
    filter_upwards [(hF k).coeFn_toL1,(hG k).coeFn_toL1] with x hx hy
    rw [hx,hy,Real.dist_eq]
  simpa only [he,L1.dist_eq_integral_dist,Real.dist_eq] using h

theorem L1_difference_density_young_bound [IsFiniteMeasure μ]
    (F G : ℕ → X → ℝ) (hF : ∀ k, Integrable (F k) μ) (hG : ∀ k, Integrable (G k) μ)
    (I J : Lp ℝ 1 μ)
    (hI : Tendsto (fun k => ∫ x, |F k x-I x| ∂μ) atTop (𝓝 0))
    (hJ : Tendsto (fun k => ∫ x, |G k x-J x| ∂μ) atTop (𝓝 0))
    (c : X → ℝ) (hc : Integrable c μ) (B a : ℝ)
    (hb : ∀ k, ∀ᵐ x ∂μ, (F k x-G k x)^2 ≤ B^2*c x) :
    4*a*(∫ x, |I x-J x| ∂μ) ≤ 4*a^2*μ.real univ+B^2*(∫ x, c x ∂μ) := by
  have hl := (integral_abs_difference_tendsto_of_L1_error μ F G hF hG I J hI hJ).const_mul (4*a)
  apply le_of_tendsto hl
  apply Eventually.of_forall
  intro k
  have hp : ∀ᵐ x ∂μ, 4*a*|F k x-G k x| ≤ 4*a^2+B^2*c x := by
    filter_upwards [hb k] with x hx
    nlinarith only [hx,sq_nonneg (2*a-|F k x-G k x|),sq_abs (F k x-G k x)]
  have hh := integral_mono_ae (((hF k).sub (hG k)).abs.const_mul (4*a))
    ((integrable_const (4*a^2)).add (hc.const_mul (B^2))) hp
  have ha := integral_add (integrable_const (4*a^2)) (hc.const_mul (B^2))
  simp only [Pi.add_apply,Pi.sub_apply] at hh
  rw [ha,integral_const_mul,integral_const_mul,integral_const] at hh
  rw [integral_const_mul] at hh
  simp only [smul_eq_mul] at hh
  nlinarith only [hh]

end RegularPointCoordinates

end

end OAI
