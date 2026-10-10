import OAI.Geometry.RCD.Metric.MetricLimitDistanceIdentification
import OAI.Analysis.RCDHeat.Foundations

namespace OAI

/-! # Finite coordinate limits give a uniform Euclidean value limit -/

open Set Filter Metric Finset
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem euclidean_norm_le_card_add_one {n : ℕ} (x : Euclidean n) {C : ℝ}
    (hC : 0≤C) (hx : ∀ i, |x i|≤C) : ‖x‖≤((n:ℝ)+1)*C := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    _≤∑ _i : Fin n, C^2 := sum_le_sum (fun i _ => by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC).mpr (hx i))
    _=(n:ℝ)*C^2 := by simp
    _≤(((n:ℝ)+1)*C)^2 := by
      have hh := mul_le_mul_of_nonneg_right (show (n:ℝ)≤((n:ℝ)+1)^2 by
        nlinarith [Nat.cast_nonneg (α:=ℝ) n]) (sq_nonneg C)
      nlinarith

theorem finite_metric_value_limit {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {n : ℕ} {S : ℝ} (p : ℕ → X) (r : ℕ → ℝ) (V : ℕ → X → Y)
    (u : ℕ → X → Euclidean n) (g : Fin n → Y → ℝ)
    (hvalues : ∀ i η, 0<η → ∀ᶠ k in atTop, ∀ x, dist x (p k)≤S*r k →
      |u k x i-g i (V k x)|<η) :
    ∀ η : ℝ, 0<η → ∀ᶠ k in atTop, ∀ x, dist x (p k)≤S*r k →
      dist (u k x) (WithLp.toLp 2 (fun i => g i (V k x)))≤η := by
  intro η hη
  let c := η/((n:ℝ)+1)
  have hc : 0<c := by dsimp [c]; positivity
  filter_upwards [Filter.eventually_all.mpr (fun i => hvalues i c hc)] with k hk
  intro x hx
  rw [dist_eq_norm]
  have hh := euclidean_norm_le_card_add_one (u k x-WithLp.toLp 2 (fun i => g i (V k x))) hc.le
    (fun i => (hk i x hx).le)
  have he : ((n:ℝ)+1)*c=η := by dsimp [c]; field_simp
  exact hh.trans_eq he

end RegularPointCoordinates

end

end OAI
