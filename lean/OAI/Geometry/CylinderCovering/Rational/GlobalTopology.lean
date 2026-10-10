import OAI.Geometry.CylinderCovering.Rational.GlobalQuantitative

namespace OAI

open Set
open scoped Topology

namespace SlopeRational

theorem mem_interior_wedge_iff (p : Plane) :
    p ∈ interior wedge ↔ 2 * |p 0| < radius (p 1) := by
  constructor
  · intro hp
    obtain ⟨ε, hε, hball⟩ :=
      Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hp)
    let q : Plane := vec2 (p 0) (p 1 + ε / 2)
    have hdist : dist q p ≤ ε / 2 := by
      rw [dist_eq_norm]
      calc
        ‖q - p‖ ≤ |(q - p) 0| + |(q - p) 1| := plane_norm_le_sum _
        _ = ε / 2 := by
          change |p 0 - p 0| + |(p 1 + ε / 2) - p 1| = ε / 2
          simp [abs_of_pos (show 0 < ε / 2 by positivity)]
    have hq := hball (show q ∈ Metric.ball p ε from hdist.trans_lt (by linarith))
    change 2 * |p 0| ≤ 1 / 2 - (p 1 + ε / 2) at hq
    unfold radius
    linarith
  · intro hp
    have hopen : IsOpen {q : Plane | 2 * |q 0| < radius (q 1)} := by
      apply isOpen_lt
      · fun_prop
      · unfold radius; fun_prop
    apply mem_interior_iff_mem_nhds.mpr
    have hsub : {q : Plane | 2 * |q 0| < radius (q 1)} ⊆ wedge := by
      intro q hq
      change 2 * |q 0| < radius (q 1) at hq
      change 2 * |q 0| ≤ radius (q 1)
      exact le_of_lt hq
    exact Filter.mem_of_superset (hopen.mem_nhds hp) hsub

theorem mem_interior_wedge_iff_walls (p : Plane) :
    p ∈ interior wedge ↔
      0 < radius (p 1) / 2 + p 0 ∧ 0 < radius (p 1) / 2 - p 0 := by
  rw [mem_interior_wedge_iff]
  constructor
  · intro h
    constructor <;> linarith [le_abs_self (p 0), neg_le_abs (p 0)]
  · rintro ⟨hplus, hminus⟩
    have ha : |p 0| < radius (p 1) / 2 := abs_lt.mpr ⟨by linarith, by linarith⟩
    linarith

theorem mem_frontier_wedge_iff (p : Plane) :
    p ∈ frontier wedge ↔ 2 * |p 0| = radius (p 1) := by
  rw [rational_wedge_isClosed.frontier_eq, mem_sdiff, mem_interior_wedge_iff]
  change (2 * |p 0| ≤ radius (p 1) ∧ ¬2 * |p 0| < radius (p 1)) ↔ _
  constructor
  · rintro ⟨hle, hnlt⟩
    exact le_antisymm hle (le_of_not_gt hnlt)
  · intro heq
    exact ⟨heq.le, by rw [heq]; exact lt_irrefl _⟩

theorem global_mem_interior_iff {d s : ℝ} (hd : 0 < d) (hs : |s| < d)
    {p : Plane} (hp : p ∈ wedge) :
    tiltedMap d s p ∈ interior wedge ↔ p ∈ interior wedge := by
  rw [mem_interior_wedge_iff_walls, mem_interior_wedge_iff_walls]
  obtain ⟨hplus, hminus⟩ := global_wall_pos_iff hd hs hp
  exact and_congr hplus hminus

theorem global_mem_frontier_iff {d s : ℝ} (hd : 0 < d) (hs : |s| < d)
    {p : Plane} (hp : p ∈ wedge) :
    tiltedMap d s p ∈ frontier wedge ↔ p ∈ frontier wedge := by
  rw [rational_wedge_isClosed.frontier_eq]
  simp only [mem_sdiff, hp, global_tiltedMap_mapsTo hd hs hp, true_and]
  exact not_congr (global_mem_interior_iff hd hs hp)

theorem global_image_interior {d s : ℝ} (hd : 0 < d) (hs : |s| < d / 4) :
    tiltedMap d s '' interior wedge = interior wedge := by
  have hsd : |s| < d := by linarith
  apply Set.Subset.antisymm
  · rintro y ⟨p, hp, rfl⟩
    exact (global_mem_interior_iff hd hsd (interior_subset hp)).2 hp
  · intro y hy
    obtain ⟨p, hp, _⟩ := rational_global_inverse hd hs (interior_subset hy)
    refine ⟨p, ?_, hp.2⟩
    exact (global_mem_interior_iff hd hsd hp.1).1 (by rwa [hp.2])

theorem global_image_frontier {d s : ℝ} (hd : 0 < d) (hs : |s| < d / 4) :
    tiltedMap d s '' frontier wedge = frontier wedge := by
  have hsd : |s| < d := by linarith
  have hsub : frontier wedge ⊆ wedge := by
    rw [rational_wedge_isClosed.frontier_eq]
    exact sdiff_subset
  apply Set.Subset.antisymm
  · rintro y ⟨p, hp, rfl⟩
    exact (global_mem_frontier_iff hd hsd (hsub hp)).2 hp
  · intro y hy
    obtain ⟨p, hp, _⟩ := rational_global_inverse hd hs (hsub hy)
    refine ⟨p, ?_, hp.2⟩
    exact (global_mem_frontier_iff hd hsd hp.1).1 (by rwa [hp.2])

end SlopeRational

end OAI
