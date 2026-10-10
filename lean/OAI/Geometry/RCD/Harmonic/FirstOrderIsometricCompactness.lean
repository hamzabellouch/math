import OAI.Geometry.RCD.Harmonic.FirstOrderMetricLimitIsometry
import OAI.Geometry.RCD.Harmonic.CenteredFirstOrderMetricCompactness

namespace OAI

/-! # The constructed moving metric limit carries the actual local isometry -/

open Set Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
universe u
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.first_order_isometric_compactness {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n) (hK : K≤0)
    (p : ℕ → X) (r ε : ℕ → ℝ)
    (hr : ∀ k, 0<r k) (hr0 : Tendsto r atTop (𝓝 0))
    (hcurv : ∀ k, -1≤K*(80*r k)^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hε0 : Tendsto ε atTop (𝓝 0))
    (U : ℕ → Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (v : ℕ → X → Euclidean n)
    (hsplit : ∀ k, FirstOrderSplittingOn (hausdorff n X) hX.quadratic
      (p k) (80*r k) (ε k) (U k) (v k)) :
    ∃ a : ℕ → ℕ, StrictMono a ∧ ∃ (Y : Type u) (dY : MetricSpace Y),
      let := dY
      ∃ (_ : ProperSpace Y) (q : Y) (δ : ℕ → ℝ) (V : ℕ → X → Y) (g : Fin n → Y → ℝ),
        (∀ k, 0<δ k ∧ δ k≤1) ∧ Tendsto δ atTop (𝓝 0) ∧
        (∀ k, IsPointedApproximation (p (a k)) q (r (a k)) 5 (δ k) (V k)) ∧
        (∀ i, LipschitzWith 2 (g i) ∧ g i q=0) ∧
        (∀ i η, 0<η → ∀ᶠ k in atTop, ∀ x, dist x (p (a k))≤5*r (a k) →
          |(v (a k) x i-v (a k) (p (a k)) i)/r (a k)-g i (V k x)|<η) ∧
        ∀ y z, dist y q<1/16 → dist z q<1/16 →
          dist (WithLp.toLp 2 (fun i => g i y)) (WithLp.toLp 2 (fun i => g i z))=dist y z := by
  have hc (k : ℕ) : -1≤K*(r k)^2 := by
    have hh := hcurv k
    have he : K*(80*r k)^2=6400*(K*(r k)^2) := by ring
    rw [he] at hh
    nlinarith
  obtain ⟨a,ha,Y,dY,hproper,q,δ,V,g,hδ,hδ0,hV,hg,hvalues⟩ :=
    hX.centered_first_order_metric_compactness hn p r ε hr hc hε hε1 hε0 U v hsplit
  let := dY
  let := hproper
  refine ⟨a,ha,Y,dY,hproper,q,δ,V,g,hδ,hδ0,hV,hg,hvalues,?_⟩
  exact hX.first_order_metric_limit_isometry hn hK (p∘a) (r∘a) (ε∘a) δ V q
    (fun k => hr (a k)) (hr0.comp ha.tendsto_atTop) (fun k => hcurv (a k))
    (fun k => hε (a k)) (fun k => hε1 (a k)) (hε0.comp ha.tendsto_atTop)
    hδ0 hV (U∘a) (v∘a) (fun k => hsplit (a k)) g (fun i => (hg i).1.continuous) hvalues

end RegularPointCoordinates

end

end OAI
