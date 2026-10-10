import OAI.Geometry.RCD.Sobolev.BoundedLocalRepresentative
import OAI.Geometry.RCD.Coordinates.UniformProductConvergence

namespace OAI

/-! # Local value convergence gives the actual normalized quadratic moments -/

open Set Metric Filter MeasureTheory
open scoped Topology BoundedContinuousFunction NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem inner_ball_value_moment_tendsto {n : ℕ} {S ρ τ : ℝ}
    (hS : 0<S) (hρ : 0<ρ) (hρτ : ρ<τ) (hτS : τ≤S)
    {μ : Measure X} {p : ℕ → X} {r ε : ℕ → ℝ} {v : ℕ → X → Euclidean n}
    (hr : ∀ k, 0<r k)
    (hv : ∀ k, IsMeasuredEuclideanApproximation μ n (p k) (r k) S (ε k) (v k))
    (hfin : ∀ k, μ (ball (p k) (S*r k))≠⊤)
    (hpos : ∀ k, 0<μ.real (ball (p k) (S*r k)))
    (hinner : ∀ k, 0<μ.real (ball (p k) (ρ*r k))) (hε : Tendsto ε atTop (𝓝 0))
    (u w : ℕ → X → ℝ) (g h : Euclidean n → ℝ) {L M : ℝ≥0}
    (hg : LipschitzOnWith L g (closedBall 0 τ)) (hh : LipschitzOnWith M h (closedBall 0 τ))
    (hprod : ∀ k, Integrable (fun x => u k x*w k x) (μ.restrict (ball (p k) (ρ*r k))))
    (hu : ∀ η : ℝ, 0<η → ∀ᶠ k in atTop,
      ∀ᵐ x ∂μ.restrict (ball (p k) (ρ*r k)), |u k x-g (v k x)|≤η)
    (hw : ∀ η : ℝ, 0<η → ∀ᶠ k in atTop,
      ∀ᵐ x ∂μ.restrict (ball (p k) (ρ*r k)), |w k x-h (v k x)|≤η) :
    Tendsto (fun k => (μ.real (ball (p k) (ρ*r k)))⁻¹*
      ∫ x in ball (p k) (ρ*r k), u k x*w k x ∂μ) atTop
      (𝓝 ((volume.real (ball (0:Euclidean n) ρ))⁻¹*(∫ z in ball 0 ρ, g z*h z))) := by
  have hτ : 0≤τ := (hρ.trans hρτ).le
  have hρS : ρ≤S := hρτ.le.trans hτS
  obtain ⟨F,hF⟩ := bounded_local_representative hτ hg
  obtain ⟨G,hG⟩ := bounded_local_representative hτ hh
  let ν := fun k => μ.restrict (ball (p k) (ρ*r k))
  let : ∀ k, IsFiniteMeasure (ν k) := fun k => ⟨by
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.mpr (measure_ne_top_of_subset
      (ball_subset_ball (mul_le_mul_of_nonneg_right hρS (hr k).le)) (hfin k))⟩
  have hmass (k : ℕ) : 0<(ν k).real univ := by
    simpa only [ν,Measure.real,Measure.restrict_apply_univ] using hinner k
  have himage : ∀ᶠ k in atTop, ∀ x∈ball (p k) (ρ*r k), v k x∈closedBall 0 τ := by
    filter_upwards [hε.eventually (Iio_mem_nhds (show 0<(τ-ρ)/3 by linarith))] with k hk x hx
    have hout : dist x (p k)≤S*r k :=
      (show dist x (p k)<ρ*r k from hx).le.trans (mul_le_mul_of_nonneg_right hρS (hr k).le)
    have hd := (abs_le.mp (pointed_radial_distance (hr k) hS.le (hv k).metric hout)).2
    have hdρ : dist x (p k)/r k<ρ := (div_lt_iff₀ (hr k)).mpr hx
    simpa only [mem_closedBall,dist_zero_right] using (show ‖v k x‖≤τ by linarith)
  have huF : ∀ η : ℝ, 0<η → ∀ᶠ k in atTop,
      ∀ᵐ x ∂ν k, |u k x-F (v k x)|≤η := by
    intro η hη
    filter_upwards [himage,hu η hη] with k hk huk
    filter_upwards [huk,ae_restrict_mem measurableSet_ball] with x hx hball
    rw [hF (hk x hball)]
    exact hx
  have hwG : ∀ η : ℝ, 0<η → ∀ᶠ k in atTop,
      ∀ᵐ x ∂ν k, |w k x-G (v k x)|≤η := by
    intro η hη
    filter_upwards [himage,hw η hη] with k hk hwk
    filter_upwards [hwk,ae_restrict_mem measurableSet_ball] with x hx hball
    rw [hG (hk x hball)]
    exact hx
  have hproduct := ae_uniform_product_convergence ν u w (fun k x => F (v k x))
    (fun k x => G (v k x)) (norm_nonneg F) (norm_nonneg G)
    (fun k => Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using F.norm_coe_le_norm (v k x))
    (fun k => Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using G.norm_coe_le_norm (v k x))
    huF hwG
  have hz := normalized_mean_tendsto_zero ν hmass
    (fun k x => u k x*w k x-F (v k x)*G (v k x)) hproduct
  have hFG (k : ℕ) : Integrable (fun x => F (v k x)*G (v k x)) (ν k) := by
    exact (integrable_const ‖F*G‖).mono'
      (((F*G).continuous.measurable.comp (hv k).measurable).aestronglyMeasurable)
      (Eventually.of_forall fun x => (F*G).norm_coe_le_norm (v k x))
  have ht := inner_ball_measured_test_tendsto hS hρ hρS hr hv hfin hpos hε (F*G)
  have htarg : (∫ z in ball (0:Euclidean n) ρ, F z*G z)=∫ z in ball 0 ρ, g z*h z := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    have hzτ : z∈closedBall (0:Euclidean n) τ :=
      closedBall_subset_closedBall hρτ.le (ball_subset_closedBall hz)
    rw [hF hzτ,hG hzτ]
  have hsum := hz.add ht
  simp only [ν,Measure.real,Measure.restrict_apply_univ,integral_sub (hprod _) (hFG _),
    BoundedContinuousFunction.coe_mul,Pi.mul_apply,mul_sub,sub_add_cancel,
    zero_add] at hsum
  rw [htarg] at hsum
  exact hsum

end RegularPointCoordinates

end

end OAI
