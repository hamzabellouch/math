import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.DistanceLayers

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem exists_distance_predecessor {V : Type*} {G : SimpleGraph V} {r v : V}
    (hv : G.Reachable r v) (hne : v ≠ r) :
    ∃ w, G.Adj v w ∧ G.Reachable r w ∧ G.dist r w + 1 = G.dist r v := by
  obtain ⟨p, hp⟩ := hv.symm.exists_walk_length_eq_dist
  rw [G.dist_comm] at hp
  cases p with
  | nil => exact False.elim (hne rfl)
  | @cons v w r hvw p =>
    refine ⟨w, hvw, p.reachable.symm, ?_⟩
    have hle : G.dist r w ≤ p.length := by
      simpa only [G.dist_comm] using G.dist_le p
    have htri := hvw.reachable.dist_triangle_right r
    have htri' := hvw.symm.reachable.dist_triangle_right r
    rw [G.dist_eq_one_iff_adj.mpr hvw] at htri
    rw [G.dist_eq_one_iff_adj.mpr hvw.symm] at htri'
    simp only [SimpleGraph.Walk.length_cons] at hp
    omega

 

structure BreadthFirstParent {V : Type*} (G : SimpleGraph V) (r : V) where
  parent : V → V
  step : ∀ v, G.Reachable r v → v ≠ r →
    G.Adj v (parent v) ∧ G.Reachable r (parent v) ∧
      G.dist r (parent v) + 1 = G.dist r v

theorem exists_breadthFirstParent {V : Type*} (G : SimpleGraph V) (r : V) :
    Nonempty (BreadthFirstParent G r) := by
  classical
  let f : V → V := fun v => if h : G.Reachable r v ∧ v ≠ r then
    (exists_distance_predecessor h.1 h.2).choose else v
  refine ⟨⟨f, ?_⟩⟩
  intro v hv hne
  dsimp [f]
  rw [dite_eq_left ⟨hv, hne⟩]
  exact (exists_distance_predecessor hv hne).choose_spec

 
theorem BreadthFirstParent.iterate_depth {V : Type*} {G : SimpleGraph V} {r : V}
    (B : BreadthFirstParent G r) {v : V} (hv : G.Reachable r v)
    (n : ℕ) (hn : n ≤ G.dist r v) :
    G.Reachable r (B.parent^[n] v) ∧ G.dist r (B.parent^[n] v) + n = G.dist r v := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    have hn' : n ≤ G.dist r v := by omega
    obtain ⟨hr, hd⟩ := ih hn'
    have hne : B.parent^[n] v ≠ r := by
      intro heq
      rw [heq, G.dist_self] at hd
      omega
    obtain ⟨ha, hr', hd'⟩ := B.step _ hr hne
    rw [Function.iterate_succ_apply']
    exact ⟨hr', by omega⟩

 
theorem BreadthFirstParent.exists_upward_walk {V : Type*} {G : SimpleGraph V} {r : V}
    (B : BreadthFirstParent G r) {v : V} (hv : G.Reachable r v)
    (n : ℕ) (hn : n ≤ G.dist r v) :
    ∃ p : G.Walk v (B.parent^[n] v), p.IsPath ∧ p.length = n ∧
      ∀ w ∈ p.support, ∃ j, j ≤ n ∧ w = B.parent^[j] v := by
  induction n with
  | zero =>
    refine ⟨.nil, by simp, rfl, ?_⟩
    intro w hw
    refine ⟨0, by omega, ?_⟩
    simpa using hw
  | succ n ih =>
    obtain ⟨p, hp, hlen, hsupp⟩ := ih (by omega)
    obtain ⟨hr, hd⟩ := B.iterate_depth hv n (by omega)
    obtain ⟨ha, _, _⟩ := B.step _ hr (by
      intro heq
      rw [heq, G.dist_self] at hd
      omega)
    have hadj : G.Adj (B.parent^[n] v) (B.parent^[n + 1] v) := by
      simpa only [Function.iterate_succ_apply'] using ha
    have hnot : B.parent^[n + 1] v ∉ p.support := by
      intro hw
      obtain ⟨j, hj, heq⟩ := hsupp _ hw
      have h₁ := (B.iterate_depth hv (n + 1) hn).2
      have h₂ := (B.iterate_depth hv j (by omega)).2
      rw [heq] at h₁
      omega
    refine ⟨p.concat hadj, hp.concat hnot hadj, by rw [SimpleGraph.Walk.length_concat, hlen], ?_⟩
    intro w hw
    rw [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at hw
    rcases hw with hw | rfl
    · obtain ⟨j, hj, heq⟩ := hsupp w hw
      exact ⟨j, by omega, heq⟩
    · exact ⟨n + 1, by omega, rfl⟩

 
def layerAncestor {V : Type*} {G : SimpleGraph V} {r : V}
    (B : BreadthFirstParent G r) (i : ℕ) (v : V) (j : ℕ) : V :=
  B.parent^[i - j] v

theorem layerAncestor_depth {V : Type*} {G : SimpleGraph V} {r v : V}
    (B : BreadthFirstParent G r) {i j : ℕ}
    (hv : v ∈ distanceLayer G r i) (hj : j ≤ i) :
    G.Reachable r (layerAncestor B i v j) ∧ G.dist r (layerAncestor B i v j) = j := by
  have h := B.iterate_depth hv.1 (i - j) (by rw [hv.2]; omega)
  rw [hv.2] at h
  exact ⟨h.1, by dsimp [layerAncestor]; omega⟩

@[simp] theorem layerAncestor_self {V : Type*} {G : SimpleGraph V} {r : V}
    (B : BreadthFirstParent G r) (i : ℕ) (v : V) : layerAncestor B i v i = v := by
  simp [layerAncestor]

theorem layerAncestor_root {V : Type*} {G : SimpleGraph V} {r v : V}
    (B : BreadthFirstParent G r) {i : ℕ} (hv : v ∈ distanceLayer G r i) :
    layerAncestor B i v 0 = r := by
  obtain ⟨hr, hd⟩ := layerAncestor_depth B hv (Nat.zero_le i)
  exact (hr.dist_eq_zero_iff.mp hd).symm

 
theorem layerAncestor_coherent {V : Type*} {G : SimpleGraph V} {r : V}
    (B : BreadthFirstParent G r) {i j l : ℕ} (hjl : j ≤ l) (hli : l ≤ i) (v : V) :
    B.parent^[l - j] (layerAncestor B i v l) = layerAncestor B i v j := by
  unfold layerAncestor
  rw [← Function.iterate_add_apply]
  congr 1
  omega

 

theorem exists_ancestor_path {V : Type*} {G : SimpleGraph V} {r v : V}
    (B : BreadthFirstParent G r) {i j : ℕ}
    (hv : v ∈ distanceLayer G r i) (hj : j ≤ i) :
    ∃ p : G.Walk v (layerAncestor B i v j), p.IsPath ∧ p.length = i - j ∧
      ∀ w ∈ p.support, j ≤ G.dist r w ∧ G.dist r w ≤ i ∧
        layerAncestor B i v (G.dist r w) = w := by
  obtain ⟨p, hp, hlen, hs⟩ := B.exists_upward_walk hv.1 (i - j) (by rw [hv.2]; omega)
  refine ⟨p, hp, hlen, ?_⟩
  intro w hw
  obtain ⟨t, ht, rfl⟩ := hs w hw
  have hd := (B.iterate_depth hv.1 t (by rw [hv.2]; omega)).2
  rw [hv.2] at hd
  refine ⟨by omega, by omega, ?_⟩
  unfold layerAncestor
  rw [show i - G.dist r (B.parent^[t] v) = t by omega]

 

theorem exists_layer_split {V : Type*} {G : SimpleGraph V} {r : V}
    (B : BreadthFirstParent G r) {i : ℕ} {S : Set V}
    (hS : S ⊆ distanceLayer G r i) (hne : ∃ x ∈ S, ∃ y ∈ S, x ≠ y) :
    ∃ d, d < i ∧ ∃ c, (∀ v ∈ S, layerAncestor B i v d = c) ∧
      ∃ x ∈ S, ∃ y ∈ S, layerAncestor B i x (d + 1) ≠ layerAncestor B i y (d + 1) := by
  classical
  obtain ⟨x, hx, y, hy, hxy⟩ := hne
  let P : ℕ → Prop := fun d => ∀ v ∈ S, layerAncestor B i v d = layerAncestor B i x d
  have h₀ : P 0 := by
    intro v hv
    rw [layerAncestor_root B (hS hv), layerAncestor_root B (hS hx)]
  let d := Nat.findGreatest P i
  have hd : d ≤ i := Nat.findGreatest_le i
  have hPd : P d := Nat.findGreatest_spec (Nat.zero_le i) h₀
  have hdlt : d < i := by
    by_contra hn
    have he : d = i := by omega
    have hh := hPd y hy
    simp only [he, layerAncestor_self] at hh
    exact hxy hh.symm
  refine ⟨d, hdlt, layerAncestor B i x d, hPd, ?_⟩
  by_contra hn
  push Not at hn
  have hPnext : P (d + 1) := by
    intro v hv
    exact hn v hv x hx
  have hh := Nat.le_findGreatest (by omega : d + 1 ≤ i) hPnext
  change d + 1 ≤ d at hh
  omega

theorem path_start_not_mem_tail {V : Type*} {G : SimpleGraph V} {x y : V}
    (p : G.Walk x y) (hp : p.IsPath) : x ∉ p.support.tail := by
  have hn := hp.support_nodup
  rw [← p.cons_tail_support, List.nodup_cons] at hn
  exact hn.1

 

theorem exists_branch_path {V : Type*} {G : SimpleGraph V} {r y z : V}
    (B : BreadthFirstParent G r) {i d : ℕ}
    (hy : y ∈ distanceLayer G r i) (hz : z ∈ distanceLayer G r i) (hd : d < i)
    (hcommon : layerAncestor B i y d = layerAncestor B i z d)
    (hbranch : layerAncestor B i y (d + 1) ≠ layerAncestor B i z (d + 1)) :
    ∃ p : G.Walk y z, p.IsPath ∧ p.length = 2 * (i - d) ∧
      ∀ w ∈ p.support, G.dist r w = i → w = y ∨ w = z := by
  obtain ⟨p, hp, hplen, hps⟩ := exists_ancestor_path B hy hd.le
  obtain ⟨q, hq, hqlen, hqs⟩ : ∃ q : G.Walk z (layerAncestor B i y d),
      q.IsPath ∧ q.length = i - d ∧ ∀ w ∈ q.support,
        d ≤ G.dist r w ∧ G.dist r w ≤ i ∧ layerAncestor B i z (G.dist r w) = w := by
    obtain ⟨q, hq, hl, hs⟩ := exists_ancestor_path B hz hd.le
    refine ⟨q.copy rfl hcommon.symm, by simpa using hq, by simpa using hl, ?_⟩
    simpa only [SimpleGraph.Walk.support_copy] using hs
  have hinter : ∀ w ∈ p.support, w ∈ q.support → w = layerAncestor B i y d := by
    intro w hw hwq
    obtain ⟨hwd, hwi, hye⟩ := hps w hw
    obtain ⟨_, _, hze⟩ := hqs w hwq
    by_cases he : G.dist r w = d
    · simpa only [he] using hye.symm
    · have hdl : d + 1 ≤ G.dist r w := by omega
      have h₁ := layerAncestor_coherent B hdl hwi y
      have h₂ := layerAncestor_coherent B hdl hwi z
      rw [hye] at h₁
      rw [hze] at h₂
      exact False.elim (hbranch (h₁.symm.trans h₂))
  refine ⟨p.append q.reverse, ?_, ?_, ?_⟩
  · rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append, List.nodup_append']
    refine ⟨hp.support_nodup, hq.reverse.support_nodup.tail, ?_⟩
    apply List.disjoint_left.mpr
    intro w hw hwq
    have hwq' : w ∈ q.support := by
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using List.mem_of_mem_tail hwq
    have he := hinter w hw hwq'
    subst w
    exact path_start_not_mem_tail q.reverse hq.reverse hwq
  · simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse, hplen, hqlen]
    omega
  · intro w hw hwi
    rw [SimpleGraph.Walk.support_append, List.mem_append] at hw
    rcases hw with hw | hw
    · have hh := (hps w hw).2.2
      simpa only [hwi, layerAncestor_self] using Or.inl hh.symm
    · have hwq : w ∈ q.support := by
        simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using List.mem_of_mem_tail hw
      have hh := (hqs w hwq).2.2
      simpa only [hwi, layerAncestor_self] using Or.inr hh.symm

 

theorem cycle_of_layer_path {V : Type*} {G : SimpleGraph V} {r y z : V} {i : ℕ}
    (p : G.Walk y z) (hp : p.IsPath)
    (hplay : ∀ w ∈ p.support, G.dist r w = i)
    (q : G.Walk y z) (hq : q.IsPath) (hqlen : 1 < q.length)
    (hqint : ∀ w ∈ q.support, G.dist r w = i → w = y ∨ w = z) :
    (p.append q.reverse).IsCycle := by
  apply hp.isCycle_append hq.reverse
  · apply List.disjoint_left.mpr
    intro w hwp hwq
    have hwp' := List.mem_of_mem_tail hwp
    have hwq' : w ∈ q.support := by
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using List.mem_of_mem_tail hwq
    rcases hqint w hwq' (hplay w hwp') with rfl | rfl
    · exact path_start_not_mem_tail p hp hwp
    · exact path_start_not_mem_tail q.reverse hq.reverse hwq
  · exact Or.inr (by simpa only [SimpleGraph.Walk.length_reverse] using hqlen)

end CycleClique

end OAI
