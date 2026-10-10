import OAI.Geometry.RCD.Metric.PointedFunctionCompactness

namespace OAI

/-! # Convergent lifts of interior Euclidean points

The lifts use the density clause of the prescribed approximation maps.
They need not be measurable: they are only countable point sequences.
-/

open Set Filter Metric
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

theorem pointed_convergent_lift {n : ℕ} {S : ℝ}
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsPointedApproximation (p k) 0 (r k) S (ε k) (v k))
    {z : Euclidean n} (hz : ‖z‖<S) :
    ∃ x : ℕ → X,
      (∀ᶠ k in atTop, dist (x k) (p k)≤S*r k) ∧
      Tendsto (fun k => v k (x k)) atTop (𝓝 z) := by
  classical
  have hex (k : ℕ) : ∃ x : X, ‖z‖≤S-ε k →
      dist x (p k)≤S*r k ∧ dist (v k x) z≤ε k := by
    by_cases h : ‖z‖≤S-ε k
    · obtain ⟨x,hx,hd⟩ := (hv k).2.2 z (by simpa only [dist_zero_right] using h)
      exact ⟨x,fun _ => ⟨hx,hd⟩⟩
    · exact ⟨p k,fun hh => (h hh).elim⟩
  choose x hx using hex
  have hroom : ∀ᶠ k in atTop, ‖z‖≤S-ε k := by
    filter_upwards [hεlim.eventually (Iio_mem_nhds (sub_pos.mpr hz))] with k hk
    linarith
  refine ⟨x,hroom.mono (fun k hk => (hx k hk).1),?_⟩
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  filter_upwards [hroom,hεlim.eventually (Iio_mem_nhds hδ)] with k hk he
  exact ((hx k hk).2).trans_lt he

/-- Uniform convergence through the given coordinate maps determines values
on every convergent lift in the physical working balls. -/
theorem pointed_uniform_values_tendsto {n : ℕ} {S : ℝ}
    (p : ℕ → X) (r : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (u : ℕ → X → ℝ) {f : Euclidean n → ℝ} (hf : Continuous f)
    (hu : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop, ∀ x,
      dist x (p k)≤S*r k → |u k x-f (v k x)|<δ)
    (x : ℕ → X) (hx : ∀ᶠ k in atTop, dist (x k) (p k)≤S*r k)
    {z : Euclidean n} (hz : Tendsto (fun k => v k (x k)) atTop (𝓝 z)) :
    Tendsto (fun k => u k (x k)) atTop (𝓝 (f z)) := by
  have he : Tendsto (fun k => u k (x k)-f (v k (x k))) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro δ hδ
    filter_upwards [hx,hu δ hδ] with k hk hu'
    simpa only [dist_zero_right,Real.norm_eq_abs] using hu' (x k) hk
  simpa only [Function.comp_def,zero_add,sub_add_cancel] using he.add ((hf.tendsto z).comp hz)

end RegularPointCoordinates

end

end OAI
