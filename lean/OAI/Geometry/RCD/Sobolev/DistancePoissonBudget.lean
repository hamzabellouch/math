import OAI.Geometry.RCD.Sobolev.DistancePoissonLocalData
import OAI.Geometry.RCD.Sobolev.CutoffLocalEnergyBound
import OAI.Geometry.RCD.Harmonic.QuadraticMeanScaling

namespace OAI

/-! # Vanishing shifted-mass budgets for the actual distance replacements -/

open Set Filter Metric MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {Q : QuadraticCheegerEnergy μ}
  {n : ℕ} {κ B J C : ℝ} {p : ℕ → X} {r : ℕ → ℝ} {hr : ∀ k, 0<r k}
  (F : DistancePoissonFamily μ Q n κ B J C p r hr)

theorem DistancePoissonFamily.shifted_budget_bound {K A Cχ : ℝ}
    (hK : K≤0) (hCχ : 0≤Cχ) (hBJ : 0≤J+B/2) (k : ℕ)
    (u : SobolevSpace μ Q)
    (χ : GoodLaplacianCutoff μ Q (p k) (12*(r k/512)) Cχ)
    (hL : ∀ᵐ x ∂μ.restrict (ball (p k) (r k/16)), localGamma μ Q u u x≤(A*r k)^2) :
    let W := (Cχ/(12*(r k/512))^2)*((J+B/2)*(r k)^2*(F.source k).real (ball (p k) (r k)))-
      K*weightedGamma μ Q χ.weight u u
    0≤W ∧ W≤(Cχ*(512/12:ℝ)^2*(J+B/2))*(F.source k).real (ball (p k) (r k))+
      (-K)*(A*r k)^2*μ.real (ball (p k) (r k)) := by
  intro W
  have hk := hr k
  have hw := χ.local_energy_le μ Q (by linarith : 2*(12*(r k/512))<r k/16) u hL
  have hv : μ.real (ball (p k) (r k/16))≤μ.real (ball (p k) (r k)) :=
    measureReal_mono (ball_subset_ball (by linarith)) measure_ball_lt_top.ne
  have hwm : weightedGamma μ Q χ.weight u u≤(A*r k)^2*μ.real (ball (p k) (r k)) :=
    hw.trans (mul_le_mul_of_nonneg_left hv (sq_nonneg _))
  have he : (Cχ/(12*(r k/512))^2)*((J+B/2)*(r k)^2*(F.source k).real (ball (p k) (r k)))=
      (Cχ*(512/12:ℝ)^2*(J+B/2))*(F.source k).real (ball (p k) (r k)) := by
    field_simp [hk.ne']
  constructor
  · dsimp only [W]
    have hnon := weightedGamma_nonneg_of_weight μ Q (Eventually.of_forall fun x => (χ.bounds x).1) u
    exact sub_nonneg.mpr ((mul_nonpos_of_nonpos_of_nonneg hK hnon).trans
      (mul_nonneg (div_nonneg hCχ (sq_nonneg _))
        (mul_nonneg (mul_nonneg hBJ (sq_nonneg _)) (measureReal_nonneg))))
  · dsimp only [W]
    rw [he]
    nlinarith only [mul_le_mul_of_nonneg_left hwm (neg_nonneg.mpr hK)]

theorem DistancePoissonFamily.normalized_shifted_budget_tendsto_zero
    {K A Cχ : ℝ} (hK : K≤0) (hCχ : 0≤Cχ) (hBJ : 0≤J+B/2)
    (u : ℕ → SobolevSpace μ Q)
    (χ : ∀ k, GoodLaplacianCutoff μ Q (p k) (12*(r k/512)) Cχ)
    (hL : ∀ k, ∀ᵐ x ∂μ.restrict (ball (p k) (r k/16)), localGamma μ Q (u k) (u k) x≤(A*r k)^2)
    (hV : ∀ k, 0<μ.real (ball (p k) (r k)))
    (hr0 : Tendsto r atTop (𝓝 0))
    (hmass : Tendsto (fun k => (F.source k).real (ball (p k) (r k))/μ.real (ball (p k) (r k)))
      atTop (𝓝 0)) :
    Tendsto (fun k => ((Cχ/(12*(r k/512))^2)*((J+B/2)*(r k)^2*(F.source k).real (ball (p k) (r k)))-
      K*weightedGamma μ Q (χ k).weight (u k) (u k))/μ.real (ball (p k) (r k))) atTop (𝓝 0) := by
  let D := Cχ*(512/12:ℝ)^2*(J+B/2)
  have hlim : Tendsto (fun k => D*((F.source k).real (ball (p k) (r k))/μ.real (ball (p k) (r k)))+
      (-K)*(A*r k)^2) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_pow (by norm_num : 2≠0),zero_add] using
      (hmass.const_mul D).add (((hr0.const_mul A).pow 2).const_mul (-K))
  apply squeeze_zero (fun k => div_nonneg (F.shifted_budget_bound hK hCχ hBJ k (u k) (χ k) (hL k)).1 (hV k).le) _ hlim
  intro k
  have hh := div_le_div_of_nonneg_right
    (F.shifted_budget_bound hK hCχ hBJ k (u k) (χ k) (hL k)).2 (hV k).le
  convert hh using 1
  dsimp only [D]
  field_simp [(hV k).ne']

end RegularPointCoordinates

end

end OAI
