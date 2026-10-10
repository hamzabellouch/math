import OAI.Geometry.RCD.Sobolev.UniformGradientEnergy
import OAI.Geometry.RCD.Sobolev.PointedEnergyCompactness

namespace OAI

/-! # The Euclidean lower energy bound from actual Sobolev sequences -/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.gradient_energy_lower_of_curvature_sequence {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n)
    {S ρ τ R : ℝ} (hS : 0<S) (hτ : 0≤τ) (hρτ : ρ<τ)
    (hτR : τ<R) (hRS : R<S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hcurv : ∀ k, -1≤K*r k^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hεlim : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (v k))
    (w : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (g : Euclidean n → ℝ) (hg : ∀ W<S, ∃ L : ℝ≥0, LipschitzOnWith L g (closedBall 0 W))
    (hconv : ∀ W : ℝ, 0<W → W<S → ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (W*r k)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k) x-g (v k x)|≤δ)
    {M C : ℝ} (hM : 0≤M)
    (hbound : ∀ k, ∀ᵐ x ∂(hausdorff n X).restrict (closedBall (p k) (R*r k)),
      r k^2*localGamma (hausdorff n X) hX.quadratic (w k) (w k) x≤M)
    (hupper : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      (r k^2/(hausdorff n X).real (ball (p k) (S*r k)))*
        (∫ x in closedBall (p k) (R*r k), localGamma (hausdorff n X) hX.quadratic
          (w k) (w k) x ∂hausdorff n X)≤C+δ) :
    IntegrableOn (fun z => ‖fderiv ℝ g z‖^2) (ball 0 ρ) volume ∧
      (∫ z in ball 0 ρ, ‖fderiv ℝ g z‖^2)≤volume.real (ball (0:Euclidean n) S)*C := by
  have hR : 0≤R := hτ.trans hτR.le
  obtain ⟨ν,t,ht,hweak,_⟩ := hX.pointed_energy_subsequence hS hR hRS hM
    p r ε v hr hε1 hεlim hv w hbound
  have hconv' (W : ℝ) (hW : 0<W) (hWS : W<S) (δ : ℝ) (hδ : 0<δ) :
      ∀ᶠ k in atTop, ∀ᵐ x ∂(hausdorff n X).restrict (ball (p (t k)) (W*r (t k))),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (w (t k)) x-g (v (t k) x)|≤δ :=
    ht.tendsto_atTop.eventually (hconv W hW hWS δ hδ)
  have hlow := hX.uniform_gradient_energy_lower hn hS hτ hρτ hτR hRS
    (p ∘ t) (r ∘ t) (ε ∘ t) (v ∘ t) (fun k => hr (t k))
    (fun k => hcurv (t k)) (fun k => hε (t k)) (fun k => hε1 (t k))
    (hεlim.comp ht.tendsto_atTop) (fun k => hv (t k)) (w ∘ t) g hg hconv' ν hweak
  have hmass : (ν.mass : ℝ)≤C := by
    have hm := (NNReal.continuous_coe.tendsto ν.mass).comp hweak.mass
    apply le_of_forall_pos_le_add
    intro δ hδ
    apply le_of_tendsto hm
    filter_upwards [ht.tendsto_atTop.eventually (hupper δ hδ)] with k hk
    have hb := FiniteMeasure.mass_map_le
      (μ := localEnergyMeasure (hausdorff n X) hX.quadratic (w (t k))
        (closedBall (p (t k)) (R*r (t k)))
        (r (t k)^2/(hausdorff n X).real (ball (p (t k)) (S*r (t k)))))
      (hv (t k)).measurable.aemeasurable
    have hb' := NNReal.coe_le_coe.mpr hb
    rw [localEnergyMeasure_mass (hausdorff n X) hX.quadratic (w (t k))
      (closedBall (p (t k)) (R*r (t k)))
      (div_nonneg (sq_nonneg (r (t k))) (show 0≤(hausdorff n X).real
        (ball (p (t k)) (S*r (t k))) from ENNReal.toReal_nonneg))] at hb'
    exact hb'.trans hk
  have hνA : (ν : Measure (Euclidean n)).real (ball 0 ρ)≤(ν.mass : ℝ) := by
    calc
      _ ≤ (ν : Measure (Euclidean n)).real univ :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (subset_univ _))
      _ = _ := by rw [Measure.real,← FiniteMeasure.ennreal_mass,ENNReal.coe_toReal]
  refine ⟨hlow.1,hlow.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_left (hνA.trans hmass) ENNReal.toReal_nonneg

end RegularPointCoordinates

end

end OAI
