import OAI.Geometry.RCD.Metric.PointedFunctionTransfer
import OAI.Geometry.RCD.Sobolev.LipschitzCompactSubsequence

namespace OAI

/-! # Uniform function compactness on varying pointed balls

The source functions are compared through the prescribed metric maps.
The limit is a genuine Lipschitz function on Euclidean space, and the
convergence is uniform on each physical source ball in this statement.
-/

open Set Metric Filter
open scoped NNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

theorem pointed_function_compactness {n : ℕ} {S A : ℝ} (hS : 0≤S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1)
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsPointedApproximation (p k) 0 (r k) S (ε k) (v k))
    (u : ℕ → X → ℝ) (L : ℝ≥0)
    (hu : ∀ k x, dist x (p k)≤S*r k → |u k x|≤A)
    (hl : ∀ k x z, dist x (p k)≤S*r k → dist z (p k)≤S*r k →
      |u k x-u k z|≤(L:ℝ)*(dist x z/r k)) :
    ∃ (g : Euclidean n → ℝ) (a : ℕ → ℕ), StrictMono a ∧ LipschitzWith L g ∧
      ∀ η : ℝ, 0<η → ∀ᶠ k in atTop, ∀ x, dist x (p (a k))≤S*r (a k) →
        |u (a k) x-g (v (a k) x)|<η := by
  choose F hF hFu hFb using fun k => pointed_function_transfer (hr k) hS
    (hε k) (hε1 k) (T := S+2) (hv k) (u k) L (hu k) (hl k)
  obtain ⟨g,a,ha,hg,_,hlim⟩ := exists_lipschitz_subsequence_on_compact
    (isCompact_closedBall (0:Euclidean n) (S+2)) F L (A+L*(S+4)) hF
    (fun k z hz => by
      have hz' : ‖z‖≤S+2 := by simpa only [mem_closedBall,dist_zero_right] using hz
      simpa only [show S+2+2=S+4 by ring] using hFb k z hz')
  have hsmall : Tendsto (fun k => (L:ℝ)*ε (a k)) atTop (𝓝 0) := by
    simpa only [mul_zero,Function.comp_def] using (hεlim.comp ha.tendsto_atTop).const_mul (L:ℝ)
  refine ⟨g,a,ha,hg,?_⟩
  intro η hη
  filter_upwards [hlim (η/2) (half_pos hη),hsmall.eventually (Iio_mem_nhds (half_pos hη))]
    with k hk he
  intro x hx
  have hnorm : ‖v (a k) x‖≤S+2 := by
    have hcenter := (hv (a k)).1
    have hd := (abs_le.mp ((hv (a k)).2.1 x (p (a k)) hx
      (by simpa only [dist_self] using mul_nonneg hS (hr (a k)).le))).2
    have hx' : dist x (p (a k))/r (a k) ≤ S := (div_le_iff₀ (hr (a k))).mpr hx
    have htri := dist_triangle (v (a k) x) (v (a k) (p (a k))) 0
    simp only [dist_zero_right] at hcenter htri
    linarith [hε1 (a k)]
  have hclose := hk (v (a k) x) (by simpa only [mem_closedBall,dist_zero_right] using hnorm)
  have hsource := hFu (a k) x hx
  have ht := abs_add_le (u (a k) x-F (a k) (v (a k) x))
    (F (a k) (v (a k) x)-g (v (a k) x))
  rw [abs_sub_comm] at hsource
  simp only [sub_add_sub_cancel] at ht
  linarith

end RegularPointCoordinates

end

end OAI
