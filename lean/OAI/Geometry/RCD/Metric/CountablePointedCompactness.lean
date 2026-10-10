import OAI.Geometry.RCD.Sobolev.CountableLipschitzCompactness
import OAI.Geometry.RCD.Metric.PointedFunctionTransfer

namespace OAI

/-! # A common subsequence for countably many local representatives -/

open Set Metric Filter
open scoped NNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

theorem countable_pointed_function_compactness {n : ℕ} {S : ℝ} (hS : 0≤S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1)
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsPointedApproximation (p k) 0 (r k) S (ε k) (v k))
    (u : ℕ → ℕ → X → ℝ) (L : ℕ → ℝ≥0) (A : ℕ → ℝ)
    (hu : ∀ m k x, dist x (p k)≤S*r k → |u m k x|≤A m)
    (hl : ∀ m k x z, dist x (p k)≤S*r k → dist z (p k)≤S*r k →
      |u m k x-u m k z|≤(L m:ℝ)*(dist x z/r k)) :
    ∃ (g : ℕ → Euclidean n → ℝ) (a : ℕ → ℕ), StrictMono a ∧
      ∀ m, LipschitzWith (L m) (g m) ∧
        ∀ η : ℝ, 0<η → ∀ᶠ k in atTop, ∀ x, dist x (p (a k))≤S*r (a k) →
          |u m (a k) x-g m (v (a k) x)|<η := by
  choose F hF hFu hFb using fun m k => pointed_function_transfer (hr k) hS
    (hε k) (hε1 k) (T := S+2) (hv k) (u m k) (L m) (hu m k) (hl m k)
  obtain ⟨g,a,ha,hg⟩ := countable_lipschitz_subsequence_on_compact
    (isCompact_closedBall (0:Euclidean n) (S+2)) F L (fun m => A m+L m*(S+4)) hF
    (fun m k z hz => by
      have hz' : ‖z‖≤S+2 := by simpa only [mem_closedBall,dist_zero_right] using hz
      simpa only [show S+2+2=S+4 by ring] using hFb m k z hz')
  refine ⟨g,a,ha,?_⟩
  intro m
  refine ⟨(hg m).1,?_⟩
  have hsmall : Tendsto (fun k => (L m:ℝ)*ε (a k)) atTop (𝓝 0) := by
    simpa only [mul_zero,Function.comp_def] using
      (hεlim.comp ha.tendsto_atTop).const_mul (L m:ℝ)
  intro η hη
  filter_upwards [(hg m).2.2 (η/2) (half_pos hη),
    hsmall.eventually (Iio_mem_nhds (half_pos hη))] with k hk he
  intro x hx
  have hnorm : ‖v (a k) x‖≤S+2 := by
    have hcenter := (hv (a k)).1
    have hd := (abs_le.mp ((hv (a k)).2.1 x (p (a k)) hx
      (by simpa only [dist_self] using mul_nonneg hS (hr (a k)).le))).2
    have hx' : dist x (p (a k))/r (a k)≤S := (div_le_iff₀ (hr (a k))).mpr hx
    have htri := dist_triangle (v (a k) x) (v (a k) (p (a k))) 0
    simp only [dist_zero_right] at hcenter htri
    linarith [hε1 (a k)]
  have hclose := hk (v (a k) x) (by simpa only [mem_closedBall,dist_zero_right] using hnorm)
  have hsource := hFu m (a k) x hx
  have ht := abs_add_le (u m (a k) x-F m (a k) (v (a k) x))
    (F m (a k) (v (a k) x)-g m (v (a k) x))
  rw [abs_sub_comm] at hsource
  simp only [sub_add_sub_cancel] at ht
  linarith

end RegularPointCoordinates

end

end OAI
