import OAI.Geometry.RCD.Sobolev.LipschitzCompactSubsequence

namespace OAI

/-! # Uniform convergence from a dense set and common Lipschitz bounds -/

open Set Filter Metric
open scoped NNReal Topology
noncomputable section
namespace RegularPointCoordinates

theorem dense_lipschitz_uniform_limit {Y : Type*} [MetricSpace Y] [CompactSpace Y]
    (d : ℕ → Y) (hd : DenseRange d) (f : ℕ → Y → ℝ) (g : Y → ℝ) (L : ℝ≥0)
    (hf : ∀ k, LipschitzWith L (f k)) (hg : LipschitzWith L g)
    (hl : ∀ i, Tendsto (fun k => f k (d i)) atTop (𝓝 (g (d i)))) :
    TendstoUniformly f g atTop := by
  classical
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  let η := ε/(2*(2*(L:ℝ)+1))
  have hη : 0 < η := by dsimp only [η]; positivity
  have hηeq : (2*(L:ℝ)+1)*η = ε/2 := by
    dsimp only [η]
    field_simp
  have hcover : (univ : Set Y) ⊆ ⋃ i, ball (d i) η := by
    intro x _
    obtain ⟨i,hi⟩ := hd.exists_dist_lt x hη
    exact mem_iUnion.mpr ⟨i,mem_ball.mpr (by simpa only [dist_comm] using hi)⟩
  obtain ⟨I,hI⟩ := isCompact_univ.elim_finite_subcover (fun i => ball (d i) η)
    (fun _ => isOpen_ball) hcover
  have he : ∀ᶠ k in atTop, ∀ i ∈ I, dist (f k (d i)) (g (d i)) < ε/2 :=
    (Filter.eventually_all_finset I).mpr fun i _ =>
      (Metric.tendsto_nhds.mp (hl i)) (ε/2) (by positivity)
  filter_upwards [he] with k hk
  intro x
  obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp (hI (mem_univ x))
  have hx : dist x (d i) < η := mem_ball.mp hxi
  have h1 := (hf k).dist_le_mul x (d i)
  have h2 := hg.dist_le_mul (d i) x
  rw [dist_comm (d i) x] at h2
  have hLη := mul_le_mul_of_nonneg_left hx.le L.coe_nonneg
  have htri := dist_triangle4 (f k x) (f k (d i)) (g (d i)) (g x)
  have hierr := hk i hi
  have hstrict : 2*(L:ℝ)*η < ε/2 := by nlinarith
  rw [dist_comm (g x) (f k x)]
  linarith

end RegularPointCoordinates

end

end OAI
