import OAI.Combinatorics.Crossing.FourCycles
import OAI.Combinatorics.Crossing.DrawnEdgeChains

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

def forwardBipartiteDart (e : BipartiteEdge m n) : (completeBipartite m n).Dart :=
  ⟨(Sum.inl e.1,Sum.inr e.2),by simp [completeBipartite,completeBipartiteGraph]⟩

def backwardBipartiteDart (e : BipartiteEdge m n) : (completeBipartite m n).Dart :=
  (forwardBipartiteDart e).symm

def bipartiteDartEdge (d : (completeBipartite m n).Dart) : BipartiteEdge m n := by
  rcases d with ⟨⟨u,v⟩,h⟩
  rcases u with i | p <;> rcases v with k | q
  · exact False.elim (by simp [completeBipartite,completeBipartiteGraph] at h)
  · exact (i,q)
  · exact (k,p)
  · exact False.elim (by simp [completeBipartite,completeBipartiteGraph] at h)

def bipartiteDartSign (d : (completeBipartite m n).Dart) : ℝ :=
  match d.fst with
  | .inl _ => 1
  | .inr _ => -1

theorem bipartiteDart_cases (d : (completeBipartite m n).Dart) :
    (∃ e, d=forwardBipartiteDart e) ∨ (∃ e, d=backwardBipartiteDart e) := by
  rcases d with ⟨⟨u,v⟩,h⟩
  rcases u with i | p <;> rcases v with k | q
  · exact False.elim (by simp [completeBipartite,completeBipartiteGraph] at h)
  · exact Or.inl ⟨(i,q),rfl⟩
  · exact Or.inr ⟨(k,p),rfl⟩
  · exact False.elim (by simp [completeBipartite,completeBipartiteGraph] at h)

theorem bipartiteDart_source_incident (d : (completeBipartite m n).Dart) :
    d.fst=Sum.inl (bipartiteDartEdge d).1 ∨ d.fst=Sum.inr (bipartiteDartEdge d).2 := by
  rcases bipartiteDart_cases d with ⟨e,rfl⟩ | ⟨e,rfl⟩
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem bipartiteDart_target_incident (d : (completeBipartite m n).Dart) :
    d.snd=Sum.inl (bipartiteDartEdge d).1 ∨ d.snd=Sum.inr (bipartiteDartEdge d).2 := by
  rcases bipartiteDart_cases d with ⟨e,rfl⟩ | ⟨e,rfl⟩
  · exact Or.inr rfl
  · exact Or.inl rfl

def dartSourceIncident (d : (completeBipartite m n).Dart) : IncidentEdges d.fst :=
  ⟨bipartiteDartEdge d,bipartiteDart_source_incident d⟩

def dartTargetIncident (d : (completeBipartite m n).Dart) : IncidentEdges d.snd :=
  ⟨bipartiteDartEdge d,bipartiteDart_target_incident d⟩

theorem bipartiteDartEdge_symm (d : (completeBipartite m n).Dart) :
    bipartiteDartEdge d.symm=bipartiteDartEdge d := by
  rcases bipartiteDart_cases d with ⟨e,rfl⟩ | ⟨e,rfl⟩ <;> rfl

theorem bipartiteDartSign_symm (d : (completeBipartite m n).Dart) :
    bipartiteDartSign d.symm= -bipartiteDartSign d := by
  rcases bipartiteDart_cases d with ⟨e,rfl⟩ | ⟨e,rfl⟩
  · rfl
  · norm_num [bipartiteDartSign,backwardBipartiteDart,forwardBipartiteDart,SimpleGraph.Dart.symm]

theorem orientedEdgeStep_dart (d : (completeBipartite m n).Dart) :
    orientedEdgeStep d.fst d.snd=bipartiteDartSign d • Pi.single (bipartiteDartEdge d) 1 := by
  rcases bipartiteDart_cases d with ⟨e,rfl⟩ | ⟨e,rfl⟩ <;>
    simp [orientedEdgeStep,bipartiteDartSign,bipartiteDartEdge,forwardBipartiteDart,
      backwardBipartiteDart,SimpleGraph.Dart.symm]

end Zarankiewicz

end

end OAI
