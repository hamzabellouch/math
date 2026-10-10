import OAI.Geometry.RCD.Metric.ExpandingPointedCompactness
import OAI.Geometry.RCD.Metric.EventualPointedCompatibility
import OAI.Geometry.RCD.Sobolev.ExhaustingLipschitzLimits
import OAI.Geometry.RCD.Metric.ApproximationRestriction

namespace OAI

/-! # A single locally uniform value limit on an expanding Euclidean domain -/

open Set Metric Filter
open scoped NNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

theorem expanding_pointed_value_limit {n : ℕ}
    (S : ℕ → ℝ) (hS : ∀ m, 0 ≤ S m) (hSlim : Tendsto S atTop atTop)
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (hεlim : Tendsto ε atTop (𝓝 0))
    (u : ℕ → X → ℝ) (L : ℕ → ℝ≥0) (A : ℕ → ℝ) (hA : ∀ m, 0 ≤ A m)
    (hdata : ∀ m, ∀ᶠ k in atTop, 0 < r k ∧ 0 ≤ ε k ∧ ε k ≤ 1 ∧
      IsPointedApproximation (p k) 0 (r k) (S m) (ε k) (v k) ∧
      (∀ x, dist x (p k) ≤ S m*r k → |u k x| ≤ A m) ∧
      (∀ x z, dist x (p k) ≤ S m*r k → dist z (p k) ≤ S m*r k →
        |u k x-u k z| ≤ (L m : ℝ)*(dist x z/r k))) :
    ∃ (a : ℕ → ℕ) (f : Euclidean n → ℝ), StrictMono a ∧ Continuous f ∧
      (∀ ρ : ℝ, ∃ C : ℝ≥0, LipschitzOnWith C f (closedBall 0 ρ)) ∧
      ∀ W : ℝ, 0 < W → ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ x,
        dist x (p (a k)) ≤ W*r (a k) → |u (a k) x-f (v (a k) x)| < η := by
  obtain ⟨g,a,ha,hg⟩ := expanding_pointed_function_compactness S hS p r ε v hεlim
    (fun _ => u) L A hA hdata
  have hcompat (i j : ℕ) : EqOn (g i) (g j) (ball 0 (min (S i) (S j))) := by
    let T := min (S i) (S j)
    have hT : 0 ≤ T := le_min (hS i) (hS j)
    have hlim : Tendsto (fun k => 3*ε (a k)) atTop (𝓝 0) := by
      simpa only [mul_zero,Function.comp_def] using (hεlim.comp ha.tendsto_atTop).const_mul 3
    apply eventual_pointed_limits_eqOn le_rfl (p∘a) (r∘a) (fun k => 3*ε (a k)) (v∘a)
      hlim (u∘a) (u∘a) (hg i).1 (hg j).1
    · filter_upwards [ha.tendsto_atTop.eventually (hdata i)] with k hk
      exact ⟨hk.1,mul_nonneg (by norm_num) hk.2.1,
        hk.2.2.2.1.restrict_radius hk.1 hT (min_le_left _ _) hk.2.1,fun _ _ => rfl⟩
    · intro η hη
      filter_upwards [(hg i).2 η hη,ha.tendsto_atTop.eventually (hdata i)] with k hk hd
      intro x hx
      exact hk x (hx.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hd.1.le))
    · intro η hη
      filter_upwards [(hg j).2 η hη,ha.tendsto_atTop.eventually (hdata j)] with k hk hd
      intro x hx
      exact hk x (hx.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hd.1.le))
  obtain ⟨f,hfc,hfg,hfL⟩ := glue_exhausting_lipschitz_balls S hSlim g L (fun m => (hg m).1) hcompat
  refine ⟨a,f,ha,hfc,hfL,?_⟩
  intro W hW η hη
  obtain ⟨m,hm⟩ := (hSlim.eventually_gt_atTop (W+2)).exists
  filter_upwards [(hg m).2 η hη,ha.tendsto_atTop.eventually (hdata m),
    (hεlim.comp ha.tendsto_atTop).eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with k hk hd he
  intro x hx
  have hxS : dist x (p (a k)) ≤ S m*r (a k) :=
    hx.trans (mul_le_mul_of_nonneg_right (by linarith) hd.1.le)
  have hvS : v (a k) x ∈ ball (0 : Euclidean n) (S m) := by
    have hc := hd.2.2.2.1.1
    have hd' := (abs_le.mp (hd.2.2.2.1.2.1 x (p (a k)) hxS
      (by simpa only [dist_self] using mul_nonneg (hS m) hd.1.le))).2
    have hrx := (div_le_iff₀ hd.1).mpr hx
    have ht := dist_triangle (v (a k) x) (v (a k) (p (a k))) 0
    simp only [mem_ball,dist_zero_right] at *
    linarith
  rw [hfg m hvS]
  exact hk x hxS

end RegularPointCoordinates

end

end OAI
