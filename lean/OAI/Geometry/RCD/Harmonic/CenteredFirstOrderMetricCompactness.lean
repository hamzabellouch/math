import OAI.Geometry.RCD.Harmonic.FirstOrderMetricCompactness
import OAI.Geometry.RCD.Metric.CenteredMetricLimit

namespace OAI

/-! # The common first-order metric limit retains the exact center -/

open Set Metric Filter MeasureTheory TopologicalSpace
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
universe u
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.centered_first_order_metric_compactness {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n)
    (p : ℕ → X) (r ε : ℕ → ℝ)
    (hr : ∀ k, 0<r k) (hcurv : ∀ k, -1≤K*(r k)^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hε0 : Tendsto ε atTop (𝓝 0))
    (u : ℕ → Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (v : ℕ → X → Euclidean n)
    (hsplit : ∀ k, FirstOrderSplittingOn (hausdorff n X) hX.quadratic
      (p k) (80*r k) (ε k) (u k) (v k)) :
    ∃ a : ℕ → ℕ, StrictMono a ∧ ∃ (Y : Type u) (dY : MetricSpace Y),
      letI := dY
      ∃ (_ : ProperSpace Y) (q : Y) (δ : ℕ → ℝ) (V : ℕ → X → Y) (g : Fin n → Y → ℝ),
        (∀ k, 0<δ k ∧ δ k≤1) ∧ Tendsto δ atTop (𝓝 0) ∧
        (∀ k, IsPointedApproximation (p (a k)) q (r (a k)) 5 (δ k) (V k)) ∧
        (∀ i, LipschitzWith 2 (g i) ∧ g i q=0) ∧
        ∀ i η, 0<η → ∀ᶠ k in atTop, ∀ x, dist x (p (a k))≤5*r (a k) →
          |(v (a k) x i-v (a k) (p (a k)) i)/r (a k)-g i (V k x)|<η := by
  obtain ⟨a,ha,Y,dY,hproper,q,δ,V,g,hδ,hδ0,hV,hg,hvalues⟩ :=
    hX.first_order_metric_compactness hn p r ε hr hcurv hε hε1 hε0 u v hsplit
  let := dY
  let := hproper
  refine ⟨a,ha,Y,dY,hproper,q,δ,V,g,hδ,hδ0,hV,?_,hvalues⟩
  intro i
  refine ⟨hg i,?_⟩
  apply centered_metric_limit_zero (p∘a) V δ
    (fun k x => (v (a k) x i-v (a k) (p (a k)) i)/r (a k)) (g i)
    (hg i).continuous.continuousAt hδ0 (fun k => (hV k).1) (by intro k; simp)
  intro η hη
  filter_upwards [hvalues i η hη] with k hk
  exact hk (p (a k)) (by
    simpa only [dist_self] using mul_nonneg (by norm_num : (0:ℝ)≤5) (hr (a k)).le)

end RegularPointCoordinates

end

end OAI
