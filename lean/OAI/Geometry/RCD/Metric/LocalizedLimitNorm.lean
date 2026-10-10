import OAI.Geometry.RCD.Metric.LocalizedMeasuredValueLimit
import OAI.Geometry.RCD.Coordinates.NormalizedL2LimitBound

namespace OAI

/-! # Exact normalized L2 bounds for localized value limits -/

open Set Metric Filter MeasureTheory
open scoped NNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem localized_limit_sq_le_one (μ : Measure X)
    {n : ℕ} {S ρ τ : ℝ} (hτ : 0≤τ) (hρτ : ρ<τ) (hτS : τ≤S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hεlim : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsMeasuredEuclideanApproximation μ n (p k) (r k) S (ε k) (v k))
    (hfin : ∀ k, μ (ball (p k) (S*r k))≠⊤)
    (hmass : ∀ k, 0<μ.real (ball (p k) (S*r k)))
    (u : ℕ → X → ℝ) (g ψ : Euclidean n → ℝ) {L M : ℝ≥0}
    (hu : ∀ k, MemLp (u k) 2 (μ.restrict (ball (p k) (S*r k))))
    (hub : ∀ k, (μ.real (ball (p k) (S*r k)))⁻¹*
      (∫ x in ball (p k) (S*r k), (u k x)^2 ∂μ)≤1)
    (hg : LipschitzOnWith L g (closedBall 0 τ)) (hψ : LipschitzWith M ψ)
    (hψb : ∀ z, |ψ z|≤1) (hψ0 : ∀ z, ρ≤‖z‖ → ψ z=0)
    (hconv : ∀ η : ℝ, 0<η → ∀ᶠ k in atTop,
      ∀ᵐ x ∂μ.restrict (ball (p k) (τ*r k)), |u k x-g (v k x)|≤η) :
    (volume.real (ball (0:Euclidean n) S))⁻¹*
      (∫ z in ball 0 S, (ψ z*g z)^2)≤1 := by
  let ν : ℕ → Measure X := fun k => μ.restrict (ball (p k) (S*r k))
  let : ∀ k, IsFiniteMeasure (ν k) := fun k =>
    ⟨by simpa only [ν,Measure.restrict_apply_univ] using lt_top_iff_ne_top.mpr (hfin k)⟩
  obtain ⟨C,hC,hF,hFb⟩ := interior_lipschitz_test_product (B := 1) hτ hg hψ hψb
    (fun z hz => hψ0 z (hρτ.le.trans hz.le))
  have hFzero (z : Euclidean n) (hz : τ<‖z‖) : ψ z*g z=0 := by
    rw [hψ0 z (hρτ.le.trans hz.le),zero_mul]
  obtain ⟨D,hD,hF2,hF2b⟩ := interior_lipschitz_test_product hτ hF.lipschitzOnWith hF hFb hFzero
  have hvalue := measured_approximation_test_tendsto hv hεlim hD hF2 hF2b
  simp only [← pow_two] at hvalue
  let U := fun k x => ψ (v k x)*u k x
  let F := fun k x => ψ (v k x)*g (v k x)
  have hU (k : ℕ) : MemLp (U k) 2 (ν k) := by
    apply (hu k).of_le_mul (c := (1:ℝ))
      (((hψ.continuous.measurable.comp (hv k).measurable).aestronglyMeasurable.mono_measure
        Measure.restrict_le_self).mul (hu k).aestronglyMeasurable)
    filter_upwards [] with x
    change |ψ (v k x)*u k x|≤1*|u k x|
    rw [abs_mul,one_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (hψb _)
  have hFF (k : ℕ) : MemLp (F k) 2 (ν k) :=
    MemLp.of_bound ((hF.continuous.measurable.comp (hv k).measurable).aestronglyMeasurable.mono_measure
      Measure.restrict_le_self) C
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hFb (v k x))
  have hUb (k : ℕ) : ((ν k).real univ)⁻¹*(∫ x, (U k x)^2 ∂ν k)≤1 := by
    have hI := integral_mono_ae (hU k).integrable_sq (hu k).integrable_sq
      (Eventually.of_forall fun x => by
        dsimp only [U]
        rw [mul_pow]
        have hb : (ψ (v k x))^2≤1 := by
          simpa only [one_pow,sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hψb (v k x)) 2
        exact mul_le_of_le_one_left (sq_nonneg _) hb)
    exact (mul_le_mul_of_nonneg_left hI (inv_nonneg.mpr (measureReal_nonneg))).trans
      (by simpa only [ν,Measure.real,Measure.restrict_apply_univ] using hub k)
  have herrors := localized_pointed_uniform_convergence μ (B := 1) zero_le_one hρτ hτS
    p r ε v hr hεlim (fun k => (hv k).metric) u g ψ hψb hψ0 hconv
  have he : Tendsto (fun k => ((ν k).real univ)⁻¹*
      (∫ x, (F k x-U k x)^2 ∂ν k)) atTop (𝓝 0) := by
    apply normalized_sq_mean_tendsto_zero ν
      (fun k => by simpa only [ν,Measure.real,Measure.restrict_apply_univ] using hmass k)
      (fun k x => F k x-U k x) (fun k => ((hFF k).sub (hU k)).aestronglyMeasurable)
    intro η hη
    filter_upwards [herrors η hη] with k hk
    refine hk.mono fun x hx => ?_
    simpa only [F,U,← mul_sub,abs_mul,abs_sub_comm] using hx
  apply normalized_L2_limit_le_one ν
    (fun k => by simpa only [ν,Measure.real,Measure.restrict_apply_univ] using hmass k)
    U F hU hFF hUb he
  simpa only [F,ν,Measure.real,Measure.restrict_apply_univ] using hvalue

end RegularPointCoordinates

end

end OAI
