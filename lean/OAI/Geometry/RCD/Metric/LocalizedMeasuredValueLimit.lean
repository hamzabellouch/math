import OAI.Geometry.RCD.Metric.LocalizedPointedConvergence
import OAI.Geometry.RCD.Sobolev.InteriorLipschitzTestProduct

namespace OAI

/-! # Weak value limits against compactly supported Lipschitz tests

Uniform local convergence controls the source error on the full outer ball.
The remaining fixed test is covered by the measured approximation itself.
-/

open Set Metric Filter MeasureTheory
open scoped NNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem localized_measured_value_limit (μ : Measure X)
    {n : ℕ} {S ρ τ : ℝ} (hτ : 0≤τ) (hρτ : ρ<τ) (hτS : τ≤S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hεlim : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsMeasuredEuclideanApproximation μ n (p k) (r k) S (ε k) (v k))
    (hfin : ∀ k, μ (ball (p k) (S*r k))≠⊤)
    (hmass : ∀ k, 0<μ.real (ball (p k) (S*r k)))
    (u : ℕ → X → ℝ) (g ψ : Euclidean n → ℝ) {L M B : ℝ≥0}
    (hu : ∀ k, IntegrableOn (u k) (ball (p k) (S*r k)) μ)
    (hg : LipschitzOnWith L g (closedBall 0 τ)) (hψ : LipschitzWith M ψ)
    (hψb : ∀ z, |ψ z|≤B) (hψ0 : ∀ z, ρ≤‖z‖ → ψ z=0)
    (hconv : ∀ η : ℝ, 0<η → ∀ᶠ k in atTop,
      ∀ᵐ x ∂μ.restrict (ball (p k) (τ*r k)), |u k x-g (v k x)|≤η) :
    Tendsto (fun k => (μ.real (ball (p k) (S*r k)))⁻¹*
      ∫ x in ball (p k) (S*r k), ψ (v k x)*u k x ∂μ) atTop
      (𝓝 ((volume.real (ball (0:Euclidean n) S))⁻¹*
        ∫ z in ball 0 S, ψ z*g z)) := by
  let ν : ℕ → Measure X := fun k => μ.restrict (ball (p k) (S*r k))
  let : ∀ k, IsFiniteMeasure (ν k) := fun k =>
    ⟨by simpa only [ν,Measure.restrict_apply_univ] using lt_top_iff_ne_top.mpr (hfin k)⟩
  obtain ⟨C,hC,hprod,hbound⟩ := interior_lipschitz_test_product hτ hg hψ hψb
    (fun z hz => hψ0 z (hρτ.le.trans hz.le))
  have htest := measured_approximation_test_tendsto hv hεlim hC hprod hbound
  have herr := normalized_mean_tendsto_zero ν
    (fun k => by simpa only [ν,Measure.real,Measure.restrict_apply_univ] using hmass k)
    (fun k x => ψ (v k x)*(u k x-g (v k x)))
    (localized_pointed_uniform_convergence μ B.coe_nonneg hρτ hτS p r ε v hr hεlim
      (fun k => (hv k).metric) u g ψ hψb hψ0 hconv)
  have hU (k : ℕ) : Integrable (fun x => ψ (v k x)*u k x) (ν k) :=
    (hu k).bdd_mul ((hψ.continuous.measurable.comp (hv k).measurable).aestronglyMeasurable.mono_measure
      Measure.restrict_le_self)
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hψb (v k x))
  have hG (k : ℕ) : Integrable (fun x => ψ (v k x)*g (v k x)) (ν k) :=
    (integrable_const (C:ℝ)).mono'
      ((hprod.continuous.measurable.comp (hv k).measurable).aestronglyMeasurable.mono_measure
        Measure.restrict_le_self)
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hbound (v k x))
  have hI (k : ℕ) : (∫ x, ψ (v k x)*(u k x-g (v k x)) ∂ν k)=
      (∫ x, ψ (v k x)*u k x ∂ν k)-(∫ x, ψ (v k x)*g (v k x) ∂ν k) := by
    simp only [mul_sub]
    exact integral_sub (hU k) (hG k)
  have heq (k : ℕ) :
      (μ.real (ball (p k) (S*r k)))⁻¹*(∫ x in ball (p k) (S*r k), ψ (v k x)*u k x ∂μ)=
      ((ν k).real univ)⁻¹*(∫ x, ψ (v k x)*(u k x-g (v k x)) ∂ν k)+
      (μ.real (ball (p k) (S*r k)))⁻¹*(∫ x in ball (p k) (S*r k), ψ (v k x)*g (v k x) ∂μ) := by
    rw [hI]
    simp only [ν,Measure.real,Measure.restrict_apply_univ]
    ring
  simpa only [zero_add,← heq] using herr.add htest

end RegularPointCoordinates

end

end OAI
