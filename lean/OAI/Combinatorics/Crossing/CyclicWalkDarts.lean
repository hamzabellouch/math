import OAI.Combinatorics.Crossing.BipartiteDartGeometry
import OAI.Combinatorics.Crossing.PeriodicPolygon

namespace OAI

noncomputable section
namespace Zarankiewicz
open SimpleGraph
variable {m n : ℕ} {u v : BipartiteVertex m n}

def walkDart (p : (completeBipartite m n).Walk u v) (i : Fin p.length) :
    (completeBipartite m n).Dart :=
  ⟨(p.getVert i.val,p.getVert (i.val+1)),p.adj_getVert_succ i.isLt⟩

theorem walkDart_eq_getElem (p : (completeBipartite m n).Walk u v) (i : Fin p.length) :
    walkDart p i=p.darts[i.val]'(by simp) :=
  (Walk.darts_getElem_eq_getVert _ _).symm

def cyclicWalkDart (p : (completeBipartite m n).Walk u u) (hp : 0 < p.length) (i : ℕ) :
    (completeBipartite m n).Dart := walkDart p (cyclicIndex p.length hp i)

theorem cyclicWalkDart_period (p : (completeBipartite m n).Walk u u) (hp : 0 < p.length) :
    cyclicWalkDart p hp p.length=cyclicWalkDart p hp 0 :=
  congrArg (walkDart p) (cyclicIndex_period _ _)

theorem cyclicWalkDart_seam (p : (completeBipartite m n).Walk u u) (hp : 0 < p.length) (i : ℕ) :
    (cyclicWalkDart p hp i).snd=(cyclicWalkDart p hp (i+1)).fst := by
  change p.getVert (i%p.length+1)=p.getVert ((i+1)%p.length)
  have hi := Nat.mod_lt i hp
  have he : (i+1)%p.length=(i%p.length+1)%p.length := by simp only [Nat.add_mod,Nat.mod_mod]
  rw [he]
  by_cases hlast : i%p.length+1=p.length
  · rw [hlast,Nat.mod_self,p.getVert_length,p.getVert_zero]
  · rw [Nat.mod_eq_of_lt (by omega : i%p.length+1<p.length)]

theorem bipartiteDart_unoriented (d : (completeBipartite m n).Dart) :
    d.edge=s(Sum.inl (bipartiteDartEdge d).1,Sum.inr (bipartiteDartEdge d).2) := by
  rcases bipartiteDart_cases d with ⟨e,rfl⟩ | ⟨e,rfl⟩
  · rfl
  · exact Sym2.eq_swap

theorem walkDart_edge_injective (p : (completeBipartite m n).Walk u v) (hp : p.IsTrail) :
    Function.Injective (fun i : Fin p.length => bipartiteDartEdge (walkDart p i)) := by
  intro i j hij
  change bipartiteDartEdge (walkDart p i)=bipartiteDartEdge (walkDart p j) at hij
  apply Fin.ext
  have hd : (walkDart p i).edge=(walkDart p j).edge := by
    rw [bipartiteDart_unoriented,bipartiteDart_unoriented,hij]
  have he : p.edges[i.val]'(by simp)=p.edges[j.val]'(by simp) := by
    simpa only [Walk.getElem_edges,walkDart,Dart.edge] using hd
  exact hp.edges_nodup.getElem_inj_iff.mp he

theorem cyclicWalkDart_next_edge_ne (p : (completeBipartite m n).Walk u u) (hp : p.IsCycle)
    (i : ℕ) :
    bipartiteDartEdge (cyclicWalkDart p (by have := hp.three_le_length; omega) (i+1)) ≠
      bipartiteDartEdge (cyclicWalkDart p (by have := hp.three_le_length; omega) i) := by
  intro he
  have hn : 1 < p.length := by have := hp.three_le_length; omega
  have hh := walkDart_edge_injective p hp.isTrail he
  have hv := congrArg Fin.val hh
  change (i+1)%p.length=i%p.length at hv
  have hi := Nat.mod_lt i (by omega : 0 < p.length)
  have hadd : (i+1)%p.length=(i%p.length+1)%p.length := by simp only [Nat.add_mod,Nat.mod_mod]
  rw [hadd] at hv
  by_cases hlast : i%p.length+1=p.length
  · rw [hlast,Nat.mod_self] at hv
    omega
  · rw [Nat.mod_eq_of_lt (by omega : i%p.length+1<p.length)] at hv
    omega

end Zarankiewicz

end

end OAI
