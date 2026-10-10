import OAI.Geometry.RCD.Sobolev.CountableCompactDomains
import OAI.Geometry.RCD.Metric.PointedFunctionTransfer

namespace OAI

/-! # One subsequence for locally bounded functions on expanding pointed balls

Only eventual data on each fixed ball is needed. Missing initial terms are
filled by zero in the compactness proof, leaving every original tail intact.
-/

open Set Metric Filter
open scoped NNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

theorem expanding_pointed_function_compactness {n : ℕ}
    (S : ℕ → ℝ) (hS : ∀ m, 0 ≤ S m)
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (hεlim : Tendsto ε atTop (𝓝 0))
    (u : ℕ → ℕ → X → ℝ) (L : ℕ → ℝ≥0) (A : ℕ → ℝ) (hA : ∀ m, 0 ≤ A m)
    (hdata : ∀ m, ∀ᶠ k in atTop, 0 < r k ∧ 0 ≤ ε k ∧ ε k ≤ 1 ∧
      IsPointedApproximation (p k) 0 (r k) (S m) (ε k) (v k) ∧
      (∀ x, dist x (p k) ≤ S m*r k → |u m k x| ≤ A m) ∧
      (∀ x z, dist x (p k) ≤ S m*r k → dist z (p k) ≤ S m*r k →
        |u m k x-u m k z| ≤ (L m : ℝ)*(dist x z/r k))) :
    ∃ (g : ℕ → Euclidean n → ℝ) (a : ℕ → ℕ), StrictMono a ∧
      ∀ m, LipschitzWith (L m) (g m) ∧
        ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ x,
          dist x (p (a k)) ≤ S m*r (a k) →
          |u m (a k) x-g m (v (a k) x)| < η := by
  classical
  have hex (m k : ℕ) : ∃ F : Euclidean n → ℝ, LipschitzWith (L m) F ∧
      (∀ y, ‖y‖ ≤ S m+2 → |F y| ≤ A m+L m*(S m+4)) ∧
      (0 < r k ∧ 0 ≤ ε k ∧ ε k ≤ 1 ∧
        IsPointedApproximation (p k) 0 (r k) (S m) (ε k) (v k) ∧
        (∀ x, dist x (p k) ≤ S m*r k → |u m k x| ≤ A m) ∧
        (∀ x z, dist x (p k) ≤ S m*r k → dist z (p k) ≤ S m*r k →
          |u m k x-u m k z| ≤ (L m : ℝ)*(dist x z/r k)) →
        ∀ x, dist x (p k) ≤ S m*r k → |F (v k x)-u m k x| ≤ L m*ε k) := by
    by_cases h : 0 < r k ∧ 0 ≤ ε k ∧ ε k ≤ 1 ∧
        IsPointedApproximation (p k) 0 (r k) (S m) (ε k) (v k) ∧
        (∀ x, dist x (p k) ≤ S m*r k → |u m k x| ≤ A m) ∧
        (∀ x z, dist x (p k) ≤ S m*r k → dist z (p k) ≤ S m*r k →
          |u m k x-u m k z| ≤ (L m : ℝ)*(dist x z/r k))
    · obtain ⟨F,hF,hFu,hFb⟩ := pointed_function_transfer h.1 (hS m) h.2.1 h.2.2.1
        (T := S m+2) h.2.2.2.1 (u m k) (L m) h.2.2.2.2.1 h.2.2.2.2.2
      exact ⟨F,hF,by simpa only [show S m+2+2=S m+4 by ring] using hFb,fun _ => hFu⟩
    · refine ⟨0,(LipschitzWith.const 0).weaken zero_le,?_,fun hh => (h hh).elim⟩
      intro y _
      simpa only [Pi.zero_apply,abs_zero] using
        add_nonneg (hA m) (mul_nonneg (L m).coe_nonneg (by linarith [hS m]))
  choose F hF hFb hFu using hex
  obtain ⟨g,a,ha,hg⟩ := countable_lipschitz_subsequence_on_compacts
    (fun m => closedBall (0 : Euclidean n) (S m+2)) (fun _ => isCompact_closedBall _ _)
    F L (fun m => A m+L m*(S m+4)) hF (by
      intro m k y hy
      exact hFb m k y (by simpa only [mem_closedBall,dist_zero_right] using hy))
  refine ⟨g,a,ha,?_⟩
  intro m
  refine ⟨(hg m).1,?_⟩
  have hsmall : Tendsto (fun k => (L m : ℝ)*ε (a k)) atTop (𝓝 0) := by
    simpa only [mul_zero,Function.comp_def] using
      (hεlim.comp ha.tendsto_atTop).const_mul (L m : ℝ)
  intro η hη
  filter_upwards [(hg m).2.2 (η/2) (half_pos hη),
    hsmall.eventually (Iio_mem_nhds (half_pos hη)),ha.tendsto_atTop.eventually (hdata m)]
    with k hk he hd
  intro x hx
  have hnorm : ‖v (a k) x‖ ≤ S m+2 := by
    have hcenter := hd.2.2.2.1.1
    have hdist := (abs_le.mp (hd.2.2.2.1.2.1 x (p (a k)) hx
      (by simpa only [dist_self] using mul_nonneg (hS m) hd.1.le))).2
    have hx' : dist x (p (a k))/r (a k) ≤ S m := (div_le_iff₀ hd.1).mpr hx
    have htri := dist_triangle (v (a k) x) (v (a k) (p (a k))) 0
    simp only [dist_zero_right] at hcenter htri
    linarith [hd.2.2.1]
  have hc := hk (v (a k) x) (by simpa only [mem_closedBall,dist_zero_right] using hnorm)
  have hs := hFu m (a k) hd x hx
  rw [abs_sub_comm] at hs
  have ht := abs_add_le (u m (a k) x-F m (a k) (v (a k) x))
    (F m (a k) (v (a k) x)-g m (v (a k) x))
  simp only [sub_add_sub_cancel] at ht
  linarith

end RegularPointCoordinates

end

end OAI
