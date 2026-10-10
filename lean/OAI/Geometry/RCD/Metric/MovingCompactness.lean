import OAI.Geometry.RCD.Metric.MovingPointedCompactness

namespace OAI

/-! # Pointed precompactness at moving centers of shrinking RCD balls -/

open Set Metric Filter
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
universe u v w

variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.movingRescalingPrecompactness {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    (p : ℕ → X) (r : ℕ → ℝ) (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ k, -1 ≤ K*(4*r (φ k))^2) ∧
      ∃ (Y : Type u) (dY : MetricSpace Y), letI := dY
        ∃ (_ : ProperSpace Y) (q : Y), PointedSequenceConverges (p ∘ φ) q (r ∘ φ) := by
  have hc0 : Tendsto (fun k => K*(r k)^2) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2:ℕ)≠0),mul_zero] using (hr0.pow 2).const_mul K
  have hc4 : Tendsto (fun k => K*(4*r k)^2) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_pow (by norm_num : (2:ℕ)≠0)] using ((hr0.const_mul 4).pow 2).const_mul K
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    ((hc0.eventually (lt_mem_nhds (by norm_num : (-1:ℝ)<0))).and
      (hc4.eventually (lt_mem_nhds (by norm_num : (-1:ℝ)<0))))
  let ps := fun k => p (k+N)
  let rs := fun k => r (k+N)
  have hrs k : 0 < rs k := hr _
  have hcs k : -1 ≤ K*(rs k)^2 := (hN _ (Nat.le_add_left _ _)).1.le
  obtain ⟨φ,hφ,Y,dY,hproper,q,hconv⟩ := hX.moving_pointed_compactness hn ps rs hrs hcs
  let := dY
  let := hproper
  refine ⟨fun k => φ k+N,?_,?_,Y,dY,hproper,q,?_⟩
  · intro i j hij
    exact Nat.add_lt_add_right (hφ hij) N
  · intro k
    exact (hN _ (Nat.le_add_left _ _)).2.le
  · simpa only [ps,rs,Function.comp_def] using hconv

end RegularPointCoordinates

end

end OAI
