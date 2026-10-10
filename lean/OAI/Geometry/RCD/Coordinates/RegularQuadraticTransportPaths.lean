import OAI.Geometry.RCD.Harmonic.DistanceQuadraticPathLimit
import OAI.Geometry.RCD.Coordinates.NearRegularPoissonFamily

namespace OAI

/-! # Absolute squared-distance path errors near every regular point

All Poisson, source, cutoff and second-order data are constructed internally.
The remaining hypotheses describe only the given compressed optimal plans.
-/

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
attribute [local instance] pathBorel pathBorelSpace

include hX in
theorem regular_quadratic_transport_paths (hn : 2≤n) (hK : K≤0)
    {o : X} (ho : IsRegular n o) (p : ℕ → X) (r : ℕ → ℝ)
    (hp : Tendsto p atTop (𝓝 o)) (hr : ∀ k, 0<r k) (hr0 : Tendsto r atTop (𝓝 0))
    (π : ℕ → Measure C(Time,X)) [∀ k, IsProbabilityMeasure (π k)]
    (hgeo : ∀ k, ∀ᵐ γ ∂π k, IsGeodesic γ)
    (hopt : ∀ k, IsOptimalCoupling ((π k).map (fun γ => γ 0)) ((π k).map (fun γ => γ 1))
      ((π k).map (fun γ => (γ 0,γ 1))))
    (Bπ : ℕ → ℝ≥0∞) (hBπ : ∀ k, Bπ k≠∞)
    (hcomp : ∀ k (t : Time), (π k).map (fun γ => γ t)≤Bπ k • hausdorff n X)
    (hs₀ : ∀ k, ∀ᵐ x ∂(π k).map (fun γ => γ 0), dist x (p k)≤r k/512)
    (hs₁ : ∀ k, ∀ᵐ x ∂(π k).map (fun γ => γ 1), dist x (p k)≤r k/512)
    {Cπ : ℝ} (hCπ : 0≤Cπ)
    (hcompression : ∀ k, (Bπ k).toReal*(hausdorff n X).real (ball (p k) (r k))≤Cπ)
    (l h t : Time) (hl : 0<(l:ℝ)) (hlh : (l:ℝ)<h) (hh : (h:ℝ)<1)
    (ht : (t:ℝ)∈Icc (l:ℝ) h) :
    Tendsto (fun k => (∫ γ, |interiorQuadraticDefect
      (fun x => dist (p k) x^2/2) l h t γ| ∂π k)/(r k)^2) atTop (𝓝 0) := by
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  obtain ⟨B,J,C,hB,hJ,_hC,N,F,hgood,_hmass,hratio,_hL2⟩ :=
    hX.near_regular_poisson_family hn hK ho p r hp hr hr0
  obtain ⟨D⟩ := hX.distance_poisson_mean_data hn hK o (neg_nonneg.mpr hK) F
    (fun k => ⟨(hgood k).1,(hgood k).2.1⟩)
  have hrN : Tendsto (fun k => r (k+N)) atTop (𝓝 0) := hr0.comp (tendsto_add_atTop_nat N)
  have hresult := D.normalized_distance_path_error (hX := hX) (hn := hn) o hK (neg_nonneg.mpr hK)
    (by positivity : 0≤J+B/2) (fun k => (hgood k).1) (fun k => (hgood k).2.2.1) hrN
    (annularPoincareConstant_pos K n).le hCπ
    (fun k => hX.annular_dirichlet_poincare hn (p (k+N)) (hr (k+N)) (hgood k).1
      (hgood k).2.2.1 (hgood k).2.2.2) hratio
    (fun k => π (k+N)) (fun k => hgeo (k+N)) (fun k => hopt (k+N))
    (fun k => Bπ (k+N)) (fun k => hBπ (k+N)) (fun k => hcomp (k+N))
    (fun k => hs₀ (k+N)) (fun k => hs₁ (k+N)) (fun k => hcompression (k+N))
    l h t hl hlh hh ht
  exact (tendsto_add_atTop_iff_nat N).mp hresult

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
