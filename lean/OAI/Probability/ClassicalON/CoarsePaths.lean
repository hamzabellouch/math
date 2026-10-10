import OAI.Probability.ClassicalON.AnnulusCut

namespace OAI

noncomputable section
open scoped Classical
namespace ClassicalON.LatticeGraph

def cellVisited (G : LatticeGraph) (η : G.edges → Bool) (x : G.vertices) (N : ℤ) (z : Site) : Prop :=
  ∃ v : G.vertices,bondConnected (fun e : G.edges => e.val.1) (fun e => e.val.2) η x v ∧ coarseSite N v.val=z

def coarseCluster (G : LatticeGraph) (η : G.edges → Bool) (x : G.vertices) (N : ℤ) : SimpleGraph Site where
  Adj z w := z≠w ∧ siteRadius z w≤1 ∧ G.cellVisited η x N z ∧ G.cellVisited η x N w
  symm := ⟨by intro z w ⟨h,hd,hz,hw⟩; exact ⟨h.symm,by simpa only [siteRadius_symm] using hd,hw,hz⟩⟩
  loopless := ⟨by intro z; simp⟩

theorem fine_edge_radius (G : LatticeGraph) (η : G.edges → Bool) {v w : G.vertices}
    (h : (bondGraph (fun e : G.edges => e.val.1) (fun e => e.val.2) η).Adj v w) :
    siteRadius v.val w.val=1 := by
  obtain ⟨_,e,_,he⟩ := h
  rcases he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact siteRadius_neighbor (G.nearest e.val e.property)
  · rw [siteRadius_symm]; exact siteRadius_neighbor (G.nearest e.val e.property)

theorem coarse_reachable_of_walk (G : LatticeGraph) (η : G.edges → Bool) (x : G.vertices)
    (N : ℤ) (hN : 0<N) {v w : G.vertices}
    (p : (bondGraph (fun e : G.edges => e.val.1) (fun e => e.val.2) η).Walk v w)
    (hv : bondConnected (fun e : G.edges => e.val.1) (fun e => e.val.2) η x v) :
    (G.coarseCluster η x N).Reachable (coarseSite N v.val) (coarseSite N w.val) := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons v w u hvw p ih =>
    have hw := bondConnected_trans _ _ _ hv ((bondConnected_iff_reachable _ _ _ _ _).mpr hvw.reachable)
    apply SimpleGraph.Reachable.trans (v := coarseSite N w.val) ?_ (ih hw)
    by_cases he : coarseSite N v.val=coarseSite N w.val
    · rw [he]
    · apply SimpleGraph.Adj.reachable
      refine ⟨he,coarseSite_step N hN (le_of_eq (G.fine_edge_radius η hvw)),⟨v,hv,rfl⟩,⟨w,hw,rfl⟩⟩

theorem coarse_walk_visited (G : LatticeGraph) (η : G.edges → Bool) (x : G.vertices)
    (N : ℤ) {z w : Site} (p : (G.coarseCluster η x N).Walk z w)
    (hz : G.cellVisited η x N z) (i : ℕ) : G.cellVisited η x N (p.getVert i) := by
  induction p generalizing i with
  | nil => exact hz
  | @cons z v w h p ih =>
    cases i with
    | zero => exact hz
    | succ i => exact ih h.2.2.2 i

theorem coarse_walk_radius (G : LatticeGraph) (η : G.edges → Bool) (x : G.vertices)
    (N : ℤ) {z w : Site} (p : (G.coarseCluster η x N).Walk z w) : siteRadius z w≤p.length := by
  induction p with
  | nil => simp
  | @cons z v w h p ih =>
    have ht := siteRadius_triangle z v w
    have hs := h.2.1
    simpa only [SimpleGraph.Walk.length_cons,Nat.cast_add,Nat.cast_one] using (show siteRadius z w≤(p.length:ℤ)+1 by omega)

theorem connected_has_coarse_code (G : LatticeGraph) (η : G.edges → Bool) (x y : G.vertices)
    (N : ℤ) (hN : 0<N) (L : ℕ) (hfar : N*((L:ℤ)+2)≤ siteRadius x.val y.val)
    (hxy : bondConnected (fun e : G.edges => e.val.1) (fun e => e.val.2) η x y) :
    ∃ c : SimpleCoarseCode (coarseSite N x.val) L,
      ∀ i : Fin (L+1),G.cellVisited η x N (codePosition (coarseSite N x.val) c.val i) := by
  obtain ⟨p⟩ := (bondConnected_iff_reachable _ _ _ _ _).mp hxy
  obtain ⟨q⟩ := G.coarse_reachable_of_walk η x N hN p (fun _ _ => rfl)
  let r := q.toPath.val
  have hr : r.IsPath := q.toPath.property
  have hl : L≤r.length := by
    have hd := coarseSite_distance N hN x.val y.val
    have hq := G.coarse_walk_radius η x N r
    by_contra hn
    have hln : (r.length:ℤ)<(L:ℤ) := by exact_mod_cast (Nat.lt_of_not_ge hn)
    nlinarith
  let a : Fin (L+1) → Site := fun i => r.getVert i.val
  have ha : Function.Injective a := by
    intro i j hij
    apply Fin.ext
    exact hr.getVert_injOn (by simp only [Set.mem_ofPred_eq]; omega) (by simp only [Set.mem_ofPred_eq]; omega) hij
  have hs (i : Fin L) : siteRadius (a i.castSucc) (a i.succ)≤1 :=
    (r.adj_getVert_succ (by omega : i.val<r.length)).2.1
  obtain ⟨c,hc⟩ := codePosition_exists a hs
  have h0 : a 0=coarseSite N x.val := r.getVert_zero
  rw [h0] at hc
  refine ⟨⟨c,hc ▸ ha⟩,?_⟩
  intro i
  rw [congrFun hc i]
  exact G.coarse_walk_visited η x N r ⟨x,(fun _ _ => rfl),rfl⟩ i.val

theorem connected_code_crossings (G : LatticeGraph) (η : G.edges → Bool) (x y : G.vertices)
    (N : ℤ) (hN : 0<N) (L : ℕ) (hfar : N*((L:ℤ)+4)≤ siteRadius x.val y.val)
    (hxy : bondConnected (fun e : G.edges => e.val.1) (fun e => e.val.2) η x y) :
    ∃ c : SimpleCoarseCode (coarseSite N x.val) L,
      ∀ i : Fin (L+1),G.annulusIndicator N (coarseCenter N (codePosition (coarseSite N x.val) c.val i)) η=1 := by
  obtain ⟨c,hc⟩ := G.connected_has_coarse_code η x y N hN L (by nlinarith) hxy
  refine ⟨c,?_⟩
  intro i
  obtain ⟨w,hw,he⟩ := hc i
  apply G.annulus_crossing_of_component N hN η x y w (by nlinarith) hxy hw
  rw [← he]
  exact le_of_lt (coarseSite_close N hN w.val)

end ClassicalON.LatticeGraph

end

end OAI
