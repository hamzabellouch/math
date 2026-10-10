import OAI.Probability.BenjaminiSchramm.IntrinsicSphere

namespace OAI

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem shortest_drop_support_distance (G : BondGraph V E) (ω : Set E)
    {x y : V} (w : (openSimpleGraph G ω).Walk x y)
    (hw : w.length = (openSimpleGraph G ω).dist x y)
    (j : ℕ) (hj : j ≤ w.length) (z : V) (hz : z ∈ (w.drop j).support) :
    j ≤ (openSimpleGraph G ω).dist x z := by
  let k := (w.drop j).support.idxOf z
  have hk : k ≤ (w.drop j).length := by
    have hh := List.idxOf_lt_length_of_mem hz
    rw [SimpleGraph.Walk.length_support] at hh
    exact Nat.le_of_lt_succ hh
  have hkj : j+k ≤ w.length := by
    rw [SimpleGraph.Walk.drop_length] at hk
    omega
  have hget : w.getVert (j+k) = z := by
    rw [←SimpleGraph.Walk.drop_getVert]
    exact (w.drop j).getVert_support_idxOf hz
  have hshort := SimpleGraph.length_eq_dist_of_subwalk hw (w.isSubwalk_take (j+k))
  rw [SimpleGraph.Walk.take_length,Nat.min_eq_left hkj,hget] at hshort
  omega

theorem intrinsic_long_connection_fresh (G : BondGraph V E) (ω : Set E)
    (x y : V) (j r : ℕ) (hj : 0 < j) (hc : Conn G ω x y)
    (hlen : j+r ≤ (openSimpleGraph G ω).dist x y) :
    ∃ z ∈ intrinsicSphere G ω x j,
      Conn G (ω \ ballIncidentEdges G (intrinsicBall G ω x (j-1))) z y ∧
      r ≤ (openSimpleGraph G (ω \ ballIncidentEdges G (intrinsicBall G ω x (j-1)))).dist z y := by
  obtain ⟨w,hw⟩ := ((conn_iff_reachable G ω x y).mp hc).exists_walk_length_eq_dist
  have hjw : j ≤ w.length := by omega
  have hzdist : (openSimpleGraph G ω).dist x (w.getVert j) = j := by
    have hh := SimpleGraph.length_eq_dist_of_subwalk hw (w.isSubwalk_take j)
    rw [SimpleGraph.Walk.take_length,Nat.min_eq_left hjw] at hh
    exact hh.symm
  have hz : w.getVert j ∈ intrinsicSphere G ω x j :=
    ⟨(conn_iff_reachable G ω x _).mpr (w.take j).reachable,hzdist⟩
  let Q := ballIncidentEdges G (intrinsicBall G ω x (j-1))
  have hsupport (z : V) (hz : z ∈ (w.drop j).support) : z ∉ intrinsicBall G ω x (j-1) := by
    intro hzB
    have hdist := shortest_drop_support_distance G ω w hw j hjw z hz
    obtain ⟨l,hl,hlen,ho⟩ := hzB
    have hle := (intrinsicBall_iff_distance_le G ω x z (j-1) (hl.conn ho)).mp ⟨l,hl,hlen,ho⟩
    omega
  have hedges : ∀ e, e ∈ (w.drop j).edges → e ∈ (openSimpleGraph G (ω \ Q)).edgeSet := by
    intro e he
    induction e using Sym2.inductionOn with
    | hf a b =>
      have hab : (openSimpleGraph G ω).Adj a b := by
        simpa using (w.drop j).edges_subset_edgeSet he
      obtain ⟨hne,f,hf,hfab⟩ := hab
      have hnot : f ∉ Q := by
        rintro ⟨z,hzB,hzf⟩
        rw [hfab] at hzf
        rcases (show z = a ∨ z = b from by simpa only [Sym2.mem_iff] using hzf) with hza | hzb
        · exact hsupport a ((w.drop j).fst_mem_support_of_mem_edges he) (hza ▸ hzB)
        · exact hsupport b ((w.drop j).snd_mem_support_of_mem_edges he) (hzb ▸ hzB)
      show (openSimpleGraph G (ω \ Q)).Adj a b
      exact ⟨hne,f,⟨hf,hnot⟩,hfab⟩
  let w' := (w.drop j).transfer (openSimpleGraph G (ω \ Q)) hedges
  have hc' : Conn G (ω \ Q) (w.getVert j) y := (conn_iff_reachable G _ _ _).mpr w'.reachable
  have hle : (openSimpleGraph G ω).dist (w.getVert j) y ≤
      (openSimpleGraph G (ω \ Q)).dist (w.getVert j) y := by
    apply SimpleGraph.Reachable.dist_anti (G := openSimpleGraph G (ω \ Q))
      (G' := openSimpleGraph G ω) _ w'.reachable
    intro a b hab
    obtain ⟨hne,e,he,heq⟩ := hab
    exact ⟨hne,e,he.1,heq⟩
  have hdrop := SimpleGraph.length_eq_dist_of_subwalk hw (w.isSubwalk_drop j)
  rw [SimpleGraph.Walk.drop_length] at hdrop
  refine ⟨w.getVert j,hz,hc',?_⟩
  change r ≤ (openSimpleGraph G (ω \ Q)).dist (w.getVert j) y
  omega

theorem intrinsic_radius_fresh_continuation (G : BondGraph V E) (ω : Set E)
    (x : V) (j r : ℕ) (hj : 0 < j)
    (hR : ω ∈ intrinsicRadiusEvent G x (j+r)) :
    ∃ z ∈ intrinsicSphere G ω x j,
      ω \ ballIncidentEdges G (intrinsicBall G ω x (j-1)) ∈ intrinsicRadiusEvent G z r := by
  obtain ⟨y,hc,hlen⟩ := hR
  obtain ⟨z,hz,hconn,hdist⟩ := intrinsic_long_connection_fresh G ω x y j r hj hc hlen
  exact ⟨z,hz,y,hconn,hdist⟩

end Percolation.BenjaminiSchramm

end OAI
