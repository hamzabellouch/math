import OAI.Geometry.RCD.Sobolev.LipschitzCompactSubsequence

namespace OAI

/-! # Compactness after subtracting the value at the center -/

open Set Filter Metric
open scoped NNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [ProperSpace X]

theorem centered_ball_subsequence (z : X) {r : ℝ} (hr : 0<r)
    (f : ℕ → X → ℝ) (L : ℝ≥0)
    (hl : ∀ k, LipschitzOnWith L (f k) (ball z (r+1))) :
    ∃ (g : closedBall z r → ℝ) (a : ℕ → ℕ), StrictMono a ∧ LipschitzWith L g ∧
      g ⟨z,mem_closedBall_self hr.le⟩=0 ∧
      TendstoUniformly (fun k (x : closedBall z r) => f (a k) x-f (a k) z) g atTop := by
  let Y := closedBall z r
  let : CompactSpace Y := isCompact_iff_compactSpace.mp (isCompact_closedBall z r)
  let U := fun k (x : Y) => f k x-f k z
  let z0 : Y := ⟨z,mem_closedBall_self hr.le⟩
  have hsub : closedBall z r ⊆ ball z (r+1) := closedBall_subset_ball (by linarith)
  have hL (k : ℕ) : LipschitzWith L (U k) := by
    have hres : LipschitzWith L (fun x : Y => f k x) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      exact (hl k).dist_le_mul x (hsub x.property) y (hsub y.property)
    simpa only [U,add_zero] using hres.sub (LipschitzWith.const (f k z))
  have hb (k : ℕ) (x : Y) : |U k x|≤(L:ℝ)*r := by
    have hh := (hL k).dist_le_mul x z0
    have hx : dist x.val z≤r := x.property
    simp only [U,z0,Real.dist_eq,sub_self,sub_zero,Subtype.dist_eq] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hx L.coe_nonneg)
  obtain ⟨g,a,ha,hg,_hgb,hlim⟩ := exists_uniform_lipschitz_subsequence U L ((L:ℝ)*r) hL hb
  refine ⟨g,a,ha,hg,?_,hlim⟩
  have hz : Tendsto (fun k => U (a k) z0) atTop (𝓝 0) := by
    simpa only [U,z0,sub_self] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
  exact tendsto_nhds_unique (hlim.tendsto_at z0) hz

end RegularPointCoordinates

end

end OAI
