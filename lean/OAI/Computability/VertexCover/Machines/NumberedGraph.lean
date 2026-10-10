import Mathlib
import OAI.Computability.VertexCover.Reduction.GraphSoundness2

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                  
section

namespace VertexCover.ExplicitGraph
noncomputable section

def numbered {n : ℕ} (G : SimpleGraph (Fin n)) : ExplicitGraph := by
  classical
  let E := (List.ofFn fun e : Fin (n*n) => finProdFinEquiv.symm e).filter
    (fun p => decide (p.1<p.2 ∧ G.Adj p.1 p.2))
  refine ⟨n,E,?_,?_⟩
  · intro p hp
    exact (of_decide_eq_true (List.mem_filter.mp hp).2).1
  · exact (List.nodup_ofFn.mpr finProdFinEquiv.symm.injective).filter _
@[simp] theorem numbered_n {n : ℕ} (G : SimpleGraph (Fin n)) : (numbered G).n=n := rfl
 theorem numbered_mem_edges {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    (u,v) ∈ (numbered G).edges ↔ u<v ∧ G.Adj u v := by
  classical
  change (u,v) ∈ ((List.ofFn fun e : Fin (n*n) => finProdFinEquiv.symm e).filter
    (fun p => decide (p.1<p.2 ∧ G.Adj p.1 p.2))) ↔ _
  simp only [List.mem_filter,List.mem_ofFn,decide_eq_true_iff]
  exact and_iff_right ⟨finProdFinEquiv (u,v),finProdFinEquiv.symm_apply_apply (u,v)⟩
 theorem numbered_cover_iff {n : ℕ} (G : SimpleGraph (Fin n)) (C : Finset (Fin n)) :
    (numbered G).Cover C ↔ G.IsVertexCover (C : Set (Fin n)) := by
  constructor
  · intro h u v huv
    rcases lt_trichotomy u v with hl | he | hg
    · exact h (u,v) ((numbered_mem_edges G u v).mpr ⟨hl,huv⟩)
    · exact (huv.ne he).elim
    · exact (h (v,u) ((numbered_mem_edges G v u).mpr ⟨hg,huv.symm⟩)).symm
  · intro h p hp
    exact h ((numbered_mem_edges G p.1 p.2).mp hp).2
 theorem numbered_complete {V : Type} [Fintype V] {n : ℕ} (G : SimpleGraph V)
    (E : Fin n ≃ V) (C : Finset V) (hc : G.IsVertexCover (C : Set V)) (ρ : ℝ)
    (hb : (C.card:ℝ) < ρ*Fintype.card V) :
    ((numbered (G.comap E)).coverNumber:ℝ) < ρ*(numbered (G.comap E)).n := by
  classical
  let S := C.map E.symm.toEmbedding
  have hs : (numbered (G.comap E)).Cover S := by
    rw [numbered_cover_iff]
    intro u v h
    exact (hc h).imp
      (fun hu => Finset.mem_map.mpr ⟨E u,hu,E.symm_apply_apply u⟩)
      (fun hv => Finset.mem_map.mpr ⟨E v,hv,E.symm_apply_apply v⟩)
  have hn : n=Fintype.card V := by simpa using Fintype.card_congr E
  have hcard : S.card=C.card := Finset.card_map _
  have hm := coverNumber_le (G := numbered (G.comap E)) S hs
  change (numbered (G.comap E)).coverNumber ≤ S.card at hm
  rw [hcard] at hm
  simpa only [numbered_n,hn] using (Nat.cast_le.mpr hm).trans_lt hb
 theorem numbered_sound {V : Type} [Fintype V] {n : ℕ} (G : SimpleGraph V)
    (E : Fin n ≃ V) (ρ : ℝ) (hb : ∀ C : Finset V, G.IsVertexCover (C : Set V) →
      ρ*Fintype.card V < (C.card:ℝ)) :
    ρ*(numbered (G.comap E)).n < ((numbered (G.comap E)).coverNumber:ℝ) := by
  classical
  obtain ⟨S,hS,hs⟩ := coverNumber_witness (numbered (G.comap E))
  let C := S.map E.toEmbedding
  have hc : G.IsVertexCover (C : Set V) := by
    intro u v huv
    have h := (numbered_cover_iff (G.comap E) S).mp hS
      (by simpa only [SimpleGraph.comap_adj,Equiv.apply_symm_apply] using huv :
        (G.comap E).Adj (E.symm u) (E.symm v))
    exact h.imp
      (fun hu => Finset.mem_map.mpr ⟨E.symm u,hu,E.apply_symm_apply u⟩)
      (fun hv => Finset.mem_map.mpr ⟨E.symm v,hv,E.apply_symm_apply v⟩)
  have hn : n=Fintype.card V := by simpa using Fintype.card_congr E
  have hcard : C.card=S.card := Finset.card_map _
  have h := hb C hc
  rw [hcard,hs] at h
  simpa only [numbered_n,hn] using h
end
end VertexCover.ExplicitGraph
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
