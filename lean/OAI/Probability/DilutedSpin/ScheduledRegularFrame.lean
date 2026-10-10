import OAI.Probability.DilutedSpin.ScheduledFrameGeometry

namespace OAI

section
section
namespace DilutedSpinGlass.DepthAverage
variable {α : Type} [Fintype α] [DecidableEq α] {L : ℕ} [NeZero L]

omit [Fintype α] [DecidableEq α] in
lemma regular_no_adjacent_values (q : α → Fin L) {η : ℝ}
    (hlarge : 1<η*(L:ℝ)) (hr : Regular η q) (a b : α) :
    (q a).val+1≠(q b).val := by
  intro he
  have hab : a≠b := by intro h; subst b; omega
  have hsep := hr.2 a b hab
  have hL : (0:ℝ)<L := Nat.cast_pos.mpr (NeZero.pos L)
  have he' : ((q a).val:ℝ)+1=((q b).val:ℝ) := by exact_mod_cast he
  have habs : |normalized (q a)-normalized (q b)|=1/(L:ℝ) := by
    unfold normalized
    rw [← sub_div,abs_div,abs_of_pos hL]
    have h : ((q a).val:ℝ)-((q b).val:ℝ) = -1 := by linarith
    rw [h]
    norm_num
  rw [habs] at hsep
  have hlt : 1/(L:ℝ)<η := (div_lt_iff₀ hL).mpr hlarge
  linarith
end DilutedSpinGlass.DepthAverage

namespace DilutedSpinGlass.ReducedTopology
open PrescribedTree
open scoped BigOperators

lemma branching_depth_assigned_at (H d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (hq : Admissible S q d (d+H)) (a : ℕ)
    (ha : a ∈ branchingDepths (realize H d S q)) : ∃ v, q v=d+a := by
  classical
  by_contra! h
  have hz : branchingCount (realize H d S q) (fun u => d+u=d+a)=0 := by
    rw [realize_branchingCount H d S q hq (fun u => u=d+a)]
    simp only [h,ite_false,Finset.sum_const_zero]
  exact ((branchingCount_eq_zero_iff _ _).mp hz a ha) rfl

lemma realize_no_adjacent_at (H d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (hq : Admissible S q d (d+H)) (hsep : ∀ u v, q u+1≠q v) :
    NoAdjacentBranchDepths (realize H d S q) := by
  intro a ha b hb he
  obtain ⟨u,hu⟩ := branching_depth_assigned_at H d S q hq a ha
  obtain ⟨v,hv⟩ := branching_depth_assigned_at H d S q hq b hb
  exact hsep u v (by omega)

/-- Genuine interior regular assignments discharge the old frame's charging
geometry, including arbitrary retained evaluation prefixes and terminal reserve. -/
theorem scheduled_regular_old_count {α : Type} [Fintype α] [DecidableEq α]
    (H r d : ℕ) (k : ℕ+) (hk : 2≤(k:ℕ)) (a : α)
    (C : Fin k → ReducedTopology) (e : (j : Fin k) → (C j).Vertex → {j : α // j≠a})
    (Q : α → Fin (H+1+1+r+1+d)) (ha : (Q a).val=r+1+d)
    (had : ∀ j, Admissible (C j) (fun v => (Q (e j v)).val) (r+1+d+1) (r+1+d+1+H))
    {η : ℝ} (hlarge : 1<η*(H+1+1+r+1+d:ℕ)) (hr : DepthAverage.Regular η Q) :
    let Base := PrescribedTree.node k (fun j => realize H (r+1+d+1) (C j) (fun v => (Q (e j v)).val))
    let Old := PrescribedTree.node k (fun j => realize (H+1) (r+1+d+1) (C j) (fun v => (Q (e j v)).val))
    branchingCount (splitFrame Old r d) (· ∈ shiftedPrefixDepths (stem Base r) d)=0 := by
  apply scheduled_frame_old_count H r d k a C e Q had
  let R : ReducedTopology := .node k hk C
  let q : R.Vertex → ℕ := rootSchedule (hk := hk) (r+1+d) (fun j v => (Q (e j v)).val)
  have hq : Admissible R q (d+1) (d+1+(H+1+r)) := by
    change d+1≤r+1+d ∧ r+1+d<d+1+(H+1+r) ∧ _
    refine ⟨by omega,by omega,?_⟩
    intro j
    simpa only [q,rootSchedule,show d+1+(H+1+r)=r+1+d+1+H by omega] using had j
  have hv (v : R.Vertex) : ∃ x : α, q v=(Q x).val := by
    cases v with
    | none => exact ⟨a,ha.symm⟩
    | some v => exact ⟨e v.1 v.2,rfl⟩
  have hno : NoAdjacentBranchDepths (realize (H+1+r) (d+1) R q) := by
    apply realize_no_adjacent_at _ _ _ _ hq
    intro u v
    obtain ⟨x,hx⟩ := hv u
    obtain ⟨y,hy⟩ := hv v
    rw [hx,hy]
    let : NeZero (H+1+1+r+1+d) := ⟨by omega⟩
    exact DepthAverage.regular_no_adjacent_values Q hlarge hr x y
  have hlower : ∀ v, d+1+r≤q v := by
    intro v
    cases v with
    | none => change d+1+r≤r+1+d; omega
    | some v =>
      have h := admissible_lower (C v.1) (fun w => (Q (e v.1 w)).val) (had v.1) v.2
      change d+1+r≤(Q (e v.1 v.2)).val
      omega
  rw [realize_stem (H+1) r (d+1) R q hlower] at hno
  change NoAdjacentBranchDepths (stem (realize (H+1) (d+1+r) (.node k hk C) q) r) at hno
  simp only [realize,q,rootSchedule,show ¬d+1+r<r+1+d by omega,ite_false] at hno
  simpa only [show d+1+r+1=r+1+d+1 by omega] using hno

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
