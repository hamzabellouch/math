import OAI.Geometry.RCD.Transport.RescaledTransportPotentials
import OAI.Geometry.RCD.Metric.PointedDualCompactness

namespace OAI

/-! # Compactness of the actual normalized RCD transport potentials -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.transport_potential_compactness {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n) {S ρ : ℝ} (hS : 0≤S) (hρ : 0≤ρ)
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1)
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsPointedApproximation (p k) 0 (r k) S (ε k) (v k))
    (ν₀ ν₁ : ℕ → ProbabilityMeasure X) (π : ℕ → Measure (X×X))
    (hac : ∀ k, (ν₀ k : Measure X) ≪ hausdorff n X)
    (hp : ∀ k, IsOptimalCoupling (ν₀ k) (ν₁ k) (π k))
    (h0 : ∀ k, ∀ᵐ x ∂(ν₀ k : Measure X), dist x (p k)≤ρ*r k)
    (h1 : ∀ k, ∀ᵐ x ∂(ν₁ k : Measure X), dist x (p k)≤ρ*r k) :
    ∃ (φ ψ : ℕ → X → ℝ) (f g : Euclidean n → ℝ) (t : ℕ → ℕ),
      (∀ k, LipschitzWith ⟨5*ρ/r k,div_nonneg (mul_nonneg (by norm_num) hρ) (hr k).le⟩ (φ k) ∧
        LipschitzWith ⟨5*ρ/r k,div_nonneg (mul_nonneg (by norm_num) hρ) (hr k).le⟩ (ψ k) ∧
        (∀ x, |φ k x|≤10*ρ^2) ∧ (∀ x, |ψ k x|≤10*ρ^2) ∧
        (∀ x y, φ k x+ψ k y≤(dist x y/r k)^2/2) ∧
        (∀ᵐ xy ∂π k, φ k xy.1+ψ k xy.2=(dist xy.1 xy.2/r k)^2/2)) ∧
      StrictMono t ∧ LipschitzWith ⟨5*ρ,by positivity⟩ f ∧
      LipschitzWith ⟨5*ρ,by positivity⟩ g ∧
      (∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop, ∀ x,
        dist x (p (t k))≤S*r (t k) → |φ (t k) x-f (v (t k) x)|<δ) ∧
      (∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop, ∀ x,
        dist x (p (t k))≤S*r (t k) → |ψ (t k) x-g (v (t k) x)|<δ) ∧
      (∀ a b : Euclidean n, ‖a‖<S → ‖b‖<S → f a+g b≤dist a b^2/2) := by
  let : SeparableSpace X := hX.separable
  let : ProperSpace X := hX.proper K n hn
  let : IsLocallyFiniteMeasure (hausdorff n X) :=
    locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
  choose φ ψ hdata using fun k => rescaled_transport_potentials (hausdorff n X)
    hX.quadratic hX.geodesic (ν₀ k : Measure X) (ν₁ k : Measure X)
    (hac k) (hp k) (p k) hρ (hr k) (h0 k) (h1 k)
  have hl (q : ℕ → X → ℝ)
      (hq : ∀ k, LipschitzWith ⟨5*ρ/r k,div_nonneg (mul_nonneg (by norm_num) hρ) (hr k).le⟩ (q k))
      (k : ℕ) (x y : X) (_hx : dist x (p k)≤S*r k) (_hy : dist y (p k)≤S*r k) :
      |q k x-q k y|≤(⟨5*ρ,by positivity⟩ : ℝ≥0)*(dist x y/r k) := by
    have hh := (hq k).dist_le_mul x y
    change dist (q k x) (q k y)≤(5*ρ/r k)*dist x y at hh
    rw [Real.dist_eq] at hh
    exact hh.trans_eq (by change (5*ρ/r k)*dist x y=(5*ρ)*(dist x y/r k); ring)
  obtain ⟨f,g,t,ht,hf,hg,hφ,hψ,had⟩ := pointed_dual_compactness hS p r ε v hr hε hε1
    hεlim hv φ ψ ⟨5*ρ,by positivity⟩
    (fun k x _ => (hdata k).2.2.1 x) (fun k x _ => (hdata k).2.2.2.1 x)
    (hl φ (fun k => (hdata k).1)) (hl ψ (fun k => (hdata k).2.1))
    (fun k => (hdata k).2.2.2.2.1)
  exact ⟨φ,ψ,f,g,t,hdata,ht,hf,hg,hφ,hψ,had⟩

end RegularPointCoordinates

end

end OAI
