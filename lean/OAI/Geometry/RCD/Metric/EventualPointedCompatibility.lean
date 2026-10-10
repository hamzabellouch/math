import OAI.Geometry.RCD.Metric.PointedLimitCompatibility

namespace OAI

/-! # Compatibility of local limits with only eventual approximation data -/

open Set Metric Filter
open scoped NNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

theorem eventual_pointed_limits_eqOn {n : ℕ} {S T : ℝ} (hTS : T ≤ S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (hεlim : Tendsto ε atTop (𝓝 0)) (u w : ℕ → X → ℝ)
    {g h : Euclidean n → ℝ} {L M : ℝ≥0}
    (hg : LipschitzWith L g) (hh : LipschitzWith M h)
    (hdata : ∀ᶠ k in atTop, 0 < r k ∧ 0 ≤ ε k ∧
      IsPointedApproximation (p k) 0 (r k) S (ε k) (v k) ∧
      ∀ x, dist x (p k) < T*r k → u k x = w k x)
    (hu : ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ x, dist x (p k) ≤ S*r k →
      |u k x-g (v k x)| < η)
    (hw : ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ x, dist x (p k) ≤ S*r k →
      |w k x-h (v k x)| < η) : EqOn g h (ball 0 T) := by
  obtain ⟨N,hN⟩ := eventually_atTop.1 hdata
  let b : ℕ → ℕ := fun k => N+k
  have hb : Tendsto b atTop atTop := by
    apply tendsto_atTop_mono (fun k => Nat.le_add_left k N) tendsto_id
  have hd (k : ℕ) := hN (b k) (Nat.le_add_right N k)
  apply pointed_limits_eqOn hTS (p∘b) (r∘b) (ε∘b) (v∘b)
    (fun k => (hd k).1) (fun k => (hd k).2.1) (hεlim.comp hb)
    (fun k => (hd k).2.2.1) (u∘b) (w∘b) hg hh (fun k => (hd k).2.2.2)
  · intro η hη
    exact hb.eventually (hu η hη)
  · intro η hη
    exact hb.eventually (hw η hη)

end RegularPointCoordinates

end

end OAI
