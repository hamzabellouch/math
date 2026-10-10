import OAI.Geometry.RCD.Harmonic.FirstOrderMetricBounds
import OAI.Geometry.RCD.Metric.PointedMetricFunctionCompactness
import OAI.Geometry.RCD.Harmonic.FiniteHarmonicLimits

namespace OAI

/-! # Common value limits of the prescribed first-order coordinate family -/

open Set Metric Filter MeasureTheory
open scoped NNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] [ProperSpace Y]
  [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.first_order_metric_value_limit {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n) (q : Y)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Y)
    (hr : ∀ k, 0<r k) (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1)
    (hε0 : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsPointedApproximation (p k) q (r k) 5 (ε k) (V k))
    (u : ℕ → Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (v : ℕ → X → Euclidean n)
    (hsplit : ∀ k, FirstOrderSplittingOn (hausdorff n X) hX.quadratic
      (p k) (80*r k) (ε k) (u k) (v k)) :
    ∃ a : ℕ → ℕ, StrictMono a ∧ ∃ g : Fin n → Y → ℝ,
      (∀ i, LipschitzWith 2 (g i)) ∧
      ∀ i η, 0<η → ∀ᶠ k in atTop, ∀ x, dist x (p (a k))≤5*r (a k) →
        |(v (a k) x i-v (a k) (p (a k)) i)/r (a k)-g i (V (a k) x)|<η := by
  let P := fun (i : Fin n) (a : ℕ → ℕ) (g : Y → ℝ) =>
    LipschitzWith 2 g ∧ ∀ η, 0<η → ∀ᶠ k in atTop,
      ∀ x, dist x (p (a k))≤5*r (a k) →
        |(v (a k) x i-v (a k) (p (a k)) i)/r (a k)-g (V (a k) x)|<η
  have hsub : ∀ i a g b, P i a g → StrictMono b → P i (a∘b) g := by
    rintro i a g b ⟨hL,hg⟩ hb
    exact ⟨hL,fun η hη => hb.tendsto_atTop.eventually (hg η hη)⟩
  have hex : ∀ a : ℕ → ℕ, StrictMono a → ∀ i, ∃ b : ℕ → ℕ, StrictMono b ∧ ∃ g, P i (a∘b) g := by
    intro a ha i
    have hb (k : ℕ) := hX.first_order_metric_bounds hn (hr (a k)) (hε (a k)) (hε1 (a k)) (hsplit (a k)) i
    obtain ⟨g,b,hbmono,hg,hconv⟩ := pointed_metric_function_compactness (by norm_num : (0:ℝ)≤5)
      (p∘a) (r∘a) (ε∘a) (V∘a) (fun k => hr (a k)) (fun k => hε (a k))
      (fun k => hε1 (a k)) (hε0.comp ha.tendsto_atTop) (fun k => hV (a k))
      (fun k x => (v (a k) x i-v (a k) (p (a k)) i)/r (a k)) 2
      (fun k => (hb k).1) (fun k => (hb k).2)
    exact ⟨b,hbmono,g,hg,hconv⟩
  obtain ⟨a,ha,g,hg⟩ := finite_subsequence_value_choice P hsub hex
  exact ⟨a,ha,g,fun i => (hg i).1,fun i => (hg i).2⟩

end RegularPointCoordinates

end

end OAI
