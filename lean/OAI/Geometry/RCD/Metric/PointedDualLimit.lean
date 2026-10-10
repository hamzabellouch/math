import OAI.Geometry.RCD.Metric.PointedApproximationLifts

namespace OAI

/-! # Local dual feasibility in the Euclidean limit -/

open Set Filter Metric
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

theorem pointed_lift_dist_tendsto {n : ℕ} {S : ℝ}
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsPointedApproximation (p k) 0 (r k) S (ε k) (v k))
    (x y : ℕ → X)
    (hx : ∀ᶠ k in atTop, dist (x k) (p k)≤S*r k)
    (hy : ∀ᶠ k in atTop, dist (y k) (p k)≤S*r k)
    {a b : Euclidean n}
    (ha : Tendsto (fun k => v k (x k)) atTop (𝓝 a))
    (hb : Tendsto (fun k => v k (y k)) atTop (𝓝 b)) :
    Tendsto (fun k => dist (x k) (y k)/r k) atTop (𝓝 (dist a b)) := by
  apply (ha.dist hb).congr_dist
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  filter_upwards [hx,hy,hεlim.eventually (Iio_mem_nhds hδ)] with k hkx hky he
  simpa only [Real.dist_eq,dist_zero_right,Real.norm_eq_abs,abs_abs] using
    ((hv k).2.1 (x k) (y k) hkx hky).trans_lt he

/-- Dual inequalities are preserved on the whole open working ball. The
assumptions here are the actual uniform values of the two source potentials. -/
theorem pointed_dual_limit {n : ℕ} {S : ℝ}
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsPointedApproximation (p k) 0 (r k) S (ε k) (v k))
    (φ ψ : ℕ → X → ℝ) {f g : Euclidean n → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (hφ : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop, ∀ x,
      dist x (p k)≤S*r k → |φ k x-f (v k x)|<δ)
    (hψ : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop, ∀ x,
      dist x (p k)≤S*r k → |ψ k x-g (v k x)|<δ)
    (had : ∀ k x y, φ k x+ψ k y≤(dist x y/r k)^2/2)
    {a b : Euclidean n} (ha : ‖a‖<S) (hb : ‖b‖<S) :
    f a+g b≤dist a b^2/2 := by
  obtain ⟨x,hx,hxa⟩ := pointed_convergent_lift p r ε v hεlim hv ha
  obtain ⟨y,hy,hyb⟩ := pointed_convergent_lift p r ε v hεlim hv hb
  have hφlim := pointed_uniform_values_tendsto p r v φ hf hφ x hx hxa
  have hψlim := pointed_uniform_values_tendsto p r v ψ hg hψ y hy hyb
  have hdist := pointed_lift_dist_tendsto p r ε v hεlim hv x y hx hy hxa hyb
  exact le_of_tendsto_of_tendsto (hφlim.add hψlim) ((hdist.pow 2).div_const 2)
    (Eventually.of_forall fun k => had k (x k) (y k))

end RegularPointCoordinates

end

end OAI
