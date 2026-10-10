import Mathlib.Topology.UniformSpace.UniformApproximation
import OAI.Geometry.NodalSets.Elliptic.RealFiniteBallJetSubsequenceLemmas

namespace OAI

namespace Yau.Geometry
open Set Metric Filter
open scoped Topology
noncomputable section

theorem real_compatible_ball_limits (W : ℕ → Yau.Jets.Coord → ℝ)
    (hW : ∀ j, Continuous (W j))
    (f : ∀ R : ℕ, closedBall (0 : Yau.Jets.Coord) (R:ℝ) → ℝ)
    (ht : ∀ R : ℕ, TendstoUniformly (fun j (x : closedBall (0 : Yau.Jets.Coord) (R:ℝ)) ↦ W j x)
      (f R) atTop) :
    ∃ g : Yau.Jets.Coord → ℝ, Continuous g ∧
      ∀ Q : Set Yau.Jets.Coord, IsCompact Q → TendstoUniformlyOn W g atTop Q := by
  choose R hR using (fun x : Yau.Jets.Coord ↦ exists_nat_gt ‖x‖)
  have hx (x : Yau.Jets.Coord) : x ∈ closedBall (0 : Yau.Jets.Coord) (R x:ℝ) := by
    simpa only [mem_closedBall,dist_zero_right] using (hR x).le
  let g (x : Yau.Jets.Coord) : ℝ := f (R x) ⟨x,hx x⟩
  have he (n : ℕ) (x : closedBall (0 : Yau.Jets.Coord) (n:ℝ)) : f n x = g x :=
    tendsto_nhds_unique ((ht n).tendsto_at x) ((ht (R x)).tendsto_at ⟨x,hx x⟩)
  have hu (n : ℕ) : TendstoUniformlyOn W g atTop (closedBall (0 : Yau.Jets.Coord) (n:ℝ)) := by
    rw [tendstoUniformlyOn_iff_restrict]
    have heq : f n = fun x : closedBall (0 : Yau.Jets.Coord) (n:ℝ) ↦ g x := funext (he n)
    change TendstoUniformly (fun j (x : closedBall (0 : Yau.Jets.Coord) (n:ℝ)) ↦ W j x)
      (fun x ↦ g x) atTop
    rw [← heq]
    exact ht n
  have hc : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro x
    have hcont := (hu (R x)).continuousOn (Filter.Eventually.frequently (Filter.Eventually.of_forall (fun j ↦ (hW j).continuousOn)))
    exact hcont.continuousAt (closedBall_mem_nhds_of_mem (by
      simpa only [mem_ball,dist_zero_right] using hR x))
  refine ⟨g,hc,?_⟩
  intro Q hQ
  obtain ⟨r,hr⟩ := hQ.isBounded.subset_closedBall (0 : Yau.Jets.Coord)
  obtain ⟨n,hn⟩ := exists_nat_gt r
  exact (hu n).mono (hr.trans (closedBall_subset_closedBall hn.le))

end
end Yau.Geometry

end OAI
