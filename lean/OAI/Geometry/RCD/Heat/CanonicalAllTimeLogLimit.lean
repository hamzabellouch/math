import OAI.Geometry.RCD.Heat.CanonicalCompactLogLimit

namespace OAI

/-! # Positive-time rescaling of the compact kernel logarithmic limit

The truncation changes only finitely many terms. This permits the fixed
reference time of the constructed heat potentials as well as interior times.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem canonicalHeatKernel_compact_log_limit_allTimes (hK : K ≤ 0)
    (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hε0 : Tendsto ε atTop (𝓝 0))
    {R T : ℝ} (hR : 0 ≤ R) (hT : 0 < T) :
    TendstoUniformly (fun k (q : closedBall p R × closedBall p R) =>
      ε k*Real.log (hX.canonicalHeatKernel hn p (ε k*T/2) q.1 q.2))
      (fun q => -dist (q.1 : X) (q.2 : X)^2/(2*T)) atTop := by
  let δ := fun k => min (2*T*ε k) 1
  have hc : 0 < 2*T := by positivity
  have he : Tendsto (fun k => 2*T*ε k) atTop (𝓝 0) := by simpa using hε0.const_mul (2*T)
  have hd : Tendsto δ atTop (𝓝 0) := by
    simpa [δ] using he.min (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  have hdpos (k : ℕ) : 0 < δ k := lt_min (mul_pos hc (hε k)) zero_lt_one
  have heq : ∀ᶠ k in atTop, δ k=2*T*ε k := by
    filter_upwards [(tendsto_order.mp he).2 1 zero_lt_one] with k hk
    exact min_eq_left hk.le
  have hl := hX.canonicalHeatKernel_compact_log_limit hn p hK δ hdpos
    (fun k => min_le_right _ _) hd hR (T := (1:ℝ)/2) (by norm_num) (by norm_num)
  apply Metric.tendstoUniformly_iff.mpr
  intro η hη
  filter_upwards [heq,(Metric.tendstoUniformly_iff.mp hl) (η*(2*T)) (mul_pos hη hc)] with k hk hh
  intro q
  have hq := hh q
  have ht : δ k*((1:ℝ)/2)/2=ε k*T/2 := by rw [hk]; ring
  simp only [ht] at hq
  simp only [hk] at hq
  norm_num at hq
  rw [Real.dist_eq] at hq ⊢
  rcases abs_lt.mp hq with ⟨ha,hb⟩
  have hcancel : (2*T)*(-dist (q.1 : X) (q.2 : X)^2/(2*T)) = -dist (q.1 : X) (q.2 : X)^2 := by
    field_simp
  apply abs_lt.mpr
  constructor <;> nlinarith

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
