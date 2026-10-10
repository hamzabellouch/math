import OAI.Probability.LatticePassage.BoundedCost
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.Set.Finite.Lemmas

namespace OAI

namespace CompanionFPP
open MeasureTheory Finset

variable {V : Type*} {G : SimpleGraph V}

lemma pathCost_eq_darts_sum (w : Weights G) {x y : V} (p : G.Walk x y) :
    pathCost w p = (p.darts.map (fun d => edgeCost w d.adj)).sum := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [ih, edgeCost]

theorem bypass_cost_le [DecidableEq V] (w : Weights G) (hw : ∀ e, 0 ≤ w e)
    {x y : V} (p : G.Walk x y) : pathCost w p.bypass ≤ pathCost w p := by
  rw [pathCost_eq_darts_sum, pathCost_eq_darts_sum]
  apply (p.darts_bypass_sublist_darts.map (fun d => edgeCost w d.adj)).sum_le_sum
  intro a ha
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp ha
  exact hw _

theorem exists_geodesic_of_bounded_cost (ω : Environment) (hw : ∀ e, 0 ≤ ω e)
    (x y : Vertex)
    (hbound : ∀ m : ℕ, ∃ R : ℕ, ∀ z, ∀ p : lattice.Walk x z,
      p.IsPath → pathCost ω p ≤ (m : ℝ) → p.length < R) :
    ∃ p : lattice.Walk x y, p.IsPath ∧ pathCost ω p = passageTime ω x y := by
  classical
  obtain ⟨q⟩ := lattice_walk x y
  obtain ⟨m,hm⟩ := exists_nat_gt (pathCost ω q)
  obtain ⟨R,hR⟩ := hbound m
  let S : Finset (Σ z : Vertex, lattice.Walk x z) :=
    (range R).biUnion fun n => startingWalks n x
  let C : Set ℝ := {c | ∃ p : lattice.Walk x y,
    p.IsPath ∧ pathCost ω p ≤ (m : ℝ) ∧ c = pathCost ω p}
  have hC : C.Finite := by
    apply (S.image (fun q => pathCost ω q.2)).finite_toSet.subset
    rintro c ⟨p,hp,hpm,rfl⟩
    apply mem_image.mpr
    refine ⟨⟨y,p⟩, ?_, rfl⟩
    exact mem_biUnion.mpr ⟨p.length, mem_range.mpr (hR y p hp hpm), trail_mem_starting p hp.isTrail⟩
  have hne : C.Nonempty :=
    ⟨pathCost ω q.bypass, q.bypass, q.bypass_isPath, (bypass_cost_le ω hw q).trans hm.le, rfl⟩
  obtain ⟨c,hc,hmin⟩ := Set.exists_min_image C id hC hne
  obtain ⟨p,hp,hpm,rfl⟩ := hc
  have hleast : ∀ r : lattice.Walk x y, pathCost ω p ≤ pathCost ω r := by
    intro r
    by_cases hr : pathCost ω r ≤ (m : ℝ)
    · have hc' : pathCost ω r.bypass ∈ C :=
        ⟨r.bypass, r.bypass_isPath, (bypass_cost_le ω hw r).trans hr, rfl⟩
      exact (hmin _ hc').trans (bypass_cost_le ω hw r)
    · exact hpm.trans (le_of_lt (lt_of_not_ge hr))
  refine ⟨p,hp,le_antisymm ?_ (passageTime_le_pathCost ω hw p)⟩
  apply le_csInf (s := Set.range (fun r : lattice.Walk x y => pathCost ω r)) ⟨_, ⟨p,rfl⟩⟩
  rintro _ ⟨r,rfl⟩
  exact hleast r

theorem geodesics_exist : ∀ᵐ ω ∂environmentLaw, ∀ x y : Vertex,
    ∃ p : lattice.Walk x y, p.IsPath ∧ pathCost ω p = passageTime ω x y := by
  filter_upwards [all_edge_weights_positive, bounded_cost_path_lengths] with ω hw hb
  intro x y
  exact exists_geodesic_of_bounded_cost ω (fun e => (hw e).le) x y (hb x)

end CompanionFPP

end OAI
