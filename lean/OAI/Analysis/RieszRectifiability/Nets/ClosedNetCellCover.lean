import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.NetDescendantCells

namespace OAI

/-!
# Covering by closed net cells

The geometric decay of lattice radii lets fine net points approximate every point of the
underlying set. Ancestor forcing places relative balls inside their closed cells, while
properness reduces nearby ancestors to finitely many choices and yields a closed-cell cover.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set Filter Topology

theorem exists_latticeRadius_tail_lt (R : ℝ) (hR : 0 < R) (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℕ, latticeRadius R (k + t + 1) < ε := by
  obtain ⟨t, ht⟩ := exists_pow_lt_of_lt_one
    (div_pos hε (latticeRadius_pos R hR (k + 1))) (by norm_num : (1 / 64 : ℝ) < 1)
  refine ⟨t, ?_⟩
  rw [show k + t + 1 = (k + 1) + t by omega, latticeRadius_add]
  simpa only [mul_comm] using! (lt_div_iff₀ (latticeRadius_pos R hR (k + 1))).mp ht

theorem relative_ball_subset_closedNetCell {X : Type*} [MetricSpace X] {E : Set X}
    (R : ℝ) (hR : 0 < R) (N : (k : ℕ) → SeparatedCover E (latticeRadius R k))
    (k : ℕ) (z : E) (hz : (z : X) ∈ (N k).points) :
    E ∩ ball (z : X) (latticeRadius R k / 8) ⊆ closedNetCell N k z := by
  rintro y ⟨hyE, hyball⟩
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨t, ht⟩ := exists_latticeRadius_tail_lt R hR k ε hε
  obtain ⟨x, hxN, hyx⟩ := (N (k + t + 1)).covers y hyE
  have hxE := (N (k + t + 1)).subset hxN
  have hscale : latticeRadius R (k + t + 1) ≤ latticeRadius R k / 64 := by
    rw [← latticeRadius_succ]
    exact latticeRadius_antitone R hR.le (by omega)
  have hxz : dist x (z : X) < latticeRadius R k / 4 := by
    have hd := dist_triangle x y (z : X)
    rw [dist_comm x y] at hd
    change dist y (z : X) < latticeRadius R k / 8 at hyball
    have hp := latticeRadius_pos R hR k
    linarith
  refine ⟨x, ⟨t + 1, hxE, ?_, netAncestor_forced_near_center R hR N k t ⟨x, hxE⟩ z hz hxz⟩,
    hyx.trans ht⟩
  simpa only [Nat.add_succ] using! hxN

theorem exists_closedNetCell_containing {X : Type*} [MetricSpace X] [ProperSpace X]
    {E : Set X} (R : ℝ) (hR : 0 < R)
    (N : (k : ℕ) → SeparatedCover E (latticeRadius R k)) (k : ℕ) (y : E) :
    ∃ z : E, (z : X) ∈ (N k).points ∧ (y : X) ∈ closedNetCell N k z := by
  classical
  let S := (N k).points ∩ closedBall (y : X) (3 * latticeRadius R k)
  have hS : S.Finite := separated_set_finite_inter_compact _ _ (latticeRadius R k)
    (latticeRadius_pos R hR k) (N k).separated (isCompact_closedBall _ _)
  let : Fintype S := hS.fintype
  let center : S → E := fun z => ⟨z, (N k).subset z.property.1⟩
  have hclosure : (y : X) ∈ closure (⋃ z : S, netDescendants N k (center z)) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨t, ht⟩ := exists_latticeRadius_tail_lt R hR k ε hε
    obtain ⟨x, hxN, hyx⟩ := (N (k + t + 1)).covers y y.property
    have hxE := (N (k + t + 1)).subset hxN
    let z := netAncestor N k (t + 1) ⟨x, hxE⟩
    have hzN : (z : X) ∈ (N k).points := netAncestor_mem N k t _
    have hzy : dist (z : X) (y : X) ≤ 3 * latticeRadius R k := by
      have hd := dist_triangle (z : X) x (y : X)
      rw [dist_comm (z : X) x, dist_comm x (y : X)] at hd
      have ha := netAncestor_dist_le_latticeRadius R hR N k (t + 1) ⟨x, hxE⟩
      have hs := latticeRadius_antitone R hR.le (show k ≤ k + t + 1 by omega)
      change dist x (z : X) ≤ _ at ha
      linarith
    let w : S := ⟨z, ⟨hzN, hzy⟩⟩
    refine ⟨x, mem_iUnion.mpr ⟨w, ?_⟩, hyx.trans ht⟩
    refine ⟨t + 1, hxE, ?_, ?_⟩
    · simpa only [Nat.add_succ] using! hxN
    · rfl
  rw [closure_iUnion_of_finite] at hclosure
  obtain ⟨z, hz⟩ := mem_iUnion.mp hclosure
  exact ⟨center z, z.property.1, hz⟩

end

end RieszRectifiability

end OAI
