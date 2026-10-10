import OAI.Probability.LatticePassage.LocalPassage
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace OAI

namespace CompanionFPP
open Finset

lemma trailCost_eq_sum (ω : Environment) {x y : Vertex} (p : lattice.Walk x y)
    (hp : p.IsTrail) : pathCost ω p = ∑ e ∈ (pathEdges p).toFinset, ω e := by
  classical
  rw [pathCost_eq_edgeList_sum]
  exact (List.sum_toFinset _ (pathEdges_nodup hp)).symm

theorem trailCost_one_edge_change (ω ω' : Environment) (e : Edge)
    (h : ∀ f, f ≠ e → ω' f = ω f) {x y : Vertex}
    (p : lattice.Walk x y) (hp : p.IsTrail) :
    pathCost ω' p - pathCost ω p =
      if e ∈ pathEdges p then ω' e - ω e else 0 := by
  classical
  rw [trailCost_eq_sum ω' p hp, trailCost_eq_sum ω p hp, ← sum_sub_distrib]
  by_cases he : e ∈ pathEdges p
  · rw [ite_eq_left he]
    apply sum_eq_single_of_mem e (List.mem_toFinset.mpr he)
    intro f _ hfe
    rw [h f hfe, sub_self]
  · rw [ite_eq_right he]
    apply sum_eq_zero
    intro f hf
    have hfe : f ≠ e := by
      intro hfe
      exact he (hfe ▸ List.mem_toFinset.mp hf)
    rw [h f hfe, sub_self]

theorem localPassageTime_one_edge_upper (ω ω' : Environment) (e : Edge)
    (h : ∀ f, f ≠ e → ω' f = ω f) {x y : Vertex} {R : ℕ}
    (p : lattice.Walk x y) (hp : p.IsPath) (hl : p.length < R)
    (hm : pathCost ω p = localPassageTime ω x y R) :
    localPassageTime ω' x y R - localPassageTime ω x y R ≤
      if e ∈ pathEdges p then ω' e - ω e else 0 := by
  classical
  have hc : localPassageTime ω' x y R ≤ pathCost ω' p :=
    csInf_le (local_costs_finite ω' x y R).bddBelow ⟨p,hp,hl,rfl⟩
  rw [← trailCost_one_edge_change ω ω' e h p hp.isTrail, ← hm]
  linarith

theorem localPassageTime_one_edge_bound (ω ω' : Environment) (e : Edge)
    (h : ∀ f, f ≠ e → ω' f = ω f) (x y : Vertex) (R : ℕ)
    (hR : latticeDistance x y < R) :
    localPassageTime ω' x y R - localPassageTime ω x y R ≤ max (ω' e - ω e) 0 := by
  obtain ⟨p,hp,hl,hm⟩ := local_geodesic_exists ω x y R hR
  apply (localPassageTime_one_edge_upper ω ω' e h p hp hl hm).trans
  split_ifs
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem localPassageTime_one_edge_lipschitz (ω ω' : Environment) (e : Edge)
    (h : ∀ f, f ≠ e → ω' f = ω f) (x y : Vertex) (R : ℕ)
    (hR : latticeDistance x y < R) :
    |localPassageTime ω' x y R - localPassageTime ω x y R| ≤ |ω' e - ω e| := by
  have h₁ := localPassageTime_one_edge_bound ω ω' e h x y R hR
  have h₂ := localPassageTime_one_edge_bound ω' ω e (fun f hf => (h f hf).symm) x y R hR
  have ha : max (ω' e - ω e) 0 ≤ |ω' e - ω e| := max_le (le_abs_self _) (abs_nonneg _)
  have hb : max (ω e - ω' e) 0 ≤ |ω' e - ω e| := by
    rw [abs_sub_comm]
    exact max_le (le_abs_self _) (abs_nonneg _)
  exact abs_le.mpr ⟨by linarith, h₁.trans ha⟩

theorem local_pathCost_change_squared (ω ω' : Environment) {x y : Vertex} {R : ℕ}
    (p : lattice.Walk x y) (hp : p.IsPath) (hl : p.length < R) :
    (pathCost ω' p - pathCost ω p)^2 ≤
      (R : ℝ) * ∑ e ∈ localEdges x R, (ω' e - ω e)^2 := by
  classical
  let s := (pathEdges p).toFinset
  have hc : s.card = p.length := by
    rw [List.toFinset_card_of_nodup (pathEdges_nodup hp.isTrail), pathEdges_length]
  have hsub : s ⊆ localEdges x R := by
    intro e he
    exact mem_biUnion.mpr ⟨⟨y,p⟩,mem_localCandidates p hp hl,he⟩
  have hsum : (∑ e ∈ s, (ω' e-ω e)^2) ≤ ∑ e ∈ localEdges x R, (ω' e-ω e)^2 :=
    sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
  have hcs := sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun e => ω' e-ω e)
  simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one, hc] at hcs
  rw [trailCost_eq_sum ω' p hp.isTrail, trailCost_eq_sum ω p hp.isTrail, ← sum_sub_distrib]
  apply hcs.trans
  gcongr

private lemma localPassageTime_change_squared_of_le (ω ω' : Environment)
    (x y : Vertex) (R : ℕ) (hR : latticeDistance x y < R)
    (hle : localPassageTime ω x y R ≤ localPassageTime ω' x y R) :
    (localPassageTime ω' x y R - localPassageTime ω x y R)^2 ≤
      (R : ℝ) * ∑ e ∈ localEdges x R, (ω' e - ω e)^2 := by
  obtain ⟨p,hp,hl,hm⟩ := local_geodesic_exists ω x y R hR
  have hc : localPassageTime ω' x y R ≤ pathCost ω' p :=
    csInf_le (local_costs_finite ω' x y R).bddBelow ⟨p,hp,hl,rfl⟩
  have hs := local_pathCost_change_squared ω ω' p hp hl
  rw [hm] at hs
  nlinarith

theorem localPassageTime_change_squared (ω ω' : Environment)
    (x y : Vertex) (R : ℕ) (hR : latticeDistance x y < R) :
    (localPassageTime ω' x y R - localPassageTime ω x y R)^2 ≤
      (R : ℝ) * ∑ e ∈ localEdges x R, (ω' e - ω e)^2 := by
  rcases le_total (localPassageTime ω x y R) (localPassageTime ω' x y R) with h | h
  · exact localPassageTime_change_squared_of_le ω ω' x y R hR h
  · simpa only [sub_sq_comm] using localPassageTime_change_squared_of_le ω' ω x y R hR h

end CompanionFPP

end OAI
