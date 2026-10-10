import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.BallPacking
import OAI.Combinatorics.Ramsey.CycleClique.Basic
import OAI.Combinatorics.Ramsey.CycleClique.CachedDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateModel
import OAI.Combinatorics.Ramsey.CycleClique.ChainProfiles
import OAI.Combinatorics.Ramsey.CycleClique.CliqueBits
import OAI.Combinatorics.Ramsey.CycleClique.CompactDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CompactLabels
import OAI.Combinatorics.Ramsey.CycleClique.EdgeBits
import OAI.Combinatorics.Ramsey.CycleClique.EdgeDecisions
import OAI.Combinatorics.Ramsey.CycleClique.ExteriorPaths
import OAI.Combinatorics.Ramsey.CycleClique.FiniteGraphs
import OAI.Combinatorics.Ramsey.CycleClique.LabelDecisions
import OAI.Combinatorics.Ramsey.CycleClique.MatrixBits
import OAI.Combinatorics.Ramsey.CycleClique.PathSystems

namespace OAI

namespace CycleClique
open scoped SimpleGraph

open scoped SimpleGraph

 
theorem outsidePath_clique_forbidden {V : Type*} [Fintype V] {G : SimpleGraph V}
    {Q : Set V} (hQ : G.IsClique Q) {k d : ℕ} (hk : 3 ≤ k)
    (ht : Q.ncard ≤ k) (hcycle : ¬ SimpleGraph.cycleGraph (k+1) ⊑ G)
    {x y : V} (hd : k+1-Q.ncard ≤ d) (hd' : d ≤ k-1) :
    ¬ OutsidePath G Q x y d := by
  classical
  rintro ⟨hx,hy,hxy,p,hp,hlen,hint⟩
  let S := (Q.toFinset.erase x).erase y
  have hs : S.card = Q.ncard-2 := by
    dsimp [S]
    rw [Finset.card_erase_of_mem (by simp [hy,hxy.symm]),
      Finset.card_erase_of_mem (by simpa using hx), ← Set.ncard_eq_toFinset_card']
    omega
  obtain ⟨T,hTS,hTc⟩ := Finset.exists_subset_card_eq (show k-1-d ≤ S.card by omega)
  let C := p.support :: T.toList.map (fun v => [v])
  have hTf : ∀ v ∈ T, v ∈ Q ∧ v ≠ x ∧ v ≠ y := by
    intro v hv
    have hh := hTS hv
    simp only [S,Finset.mem_erase,Set.mem_toFinset] at hh
    exact ⟨hh.2.2,hh.2.1,hh.1⟩
  have hf : C.flatten = p.support ++ T.toList := by simp [C,flatten_singletons]
  have hnd : C.flatten.Nodup := by
    rw [hf,List.nodup_append]
    refine ⟨hp.support_nodup,Finset.nodup_toList _,?_⟩
    intro a ha b hb hab
    subst b
    have hh := hTf a (Finset.mem_toList.mp hb)
    exact (hint a ha hh.1).elim hh.2.1 hh.2.2
  have hc := close_clique_chains hQ C (by
    intro c hc
    simp only [C,List.mem_cons,List.mem_map] at hc
    rcases hc with rfl | ⟨v,hv,rfl⟩
    · exact p.support_ne_nil
    · simp) hnd (by
    intro c hc
    simp only [C,List.mem_cons,List.mem_map] at hc
    rcases hc with rfl | ⟨v,hv,rfl⟩
    · exact p.isChain_adj_support
    · simp) (by
    intro c hc
    simp only [C,List.mem_cons,List.mem_map] at hc
    rcases hc with rfl | ⟨v,hv,rfl⟩
    · constructor
      · intro u hu
        have : u=x := by simpa [List.head?_eq_some_head p.support_ne_nil] using hu.symm
        simpa [this] using hx
      · intro u hu
        have : u=y := by simpa [List.getLast?_eq_some_getLast p.support_ne_nil] using hu.symm
        simpa [this] using hy
    · have hvQ := (hTf v (Finset.mem_toList.mp hv)).1
      simpa using And.intro hvQ hvQ) (by
    rw [hf,List.length_append,SimpleGraph.Walk.length_support,Finset.length_toList,hTc]
    omega)
  have hcL : C.flatten.length = k+1 := by
    rw [hf,List.length_append,SimpleGraph.Walk.length_support,Finset.length_toList,hTc]
    omega
  exact hcycle (hcL ▸ hc)

 
theorem outsidePath_of_list {V : Type*} {G : SimpleGraph V} {Q : Set V}
    {x y : V} {d : ℕ} (L : List V) (hL : L.Nodup) (hchain : L.IsChain G.Adj)
    (hfirst : L.head? = some x) (hlast : L.getLast? = some y)
    (hlen : L.length = d+2) (hx : x ∈ Q) (hy : y ∈ Q)
    (hint : ∀ v ∈ L, v ∈ Q → v=x ∨ v=y) : OutsidePath G Q x y d := by
  have hne : L ≠ [] := by intro he; simp [he] at hfirst
  let p := SimpleGraph.Walk.ofSupport L hne hchain
  have he₁ : L.head hne=x := by simpa only [List.head?_eq_some_head hne,Option.some.injEq] using hfirst
  have he₂ : L.getLast hne=y := by simpa only [List.getLast?_eq_some_getLast hne,Option.some.injEq] using hlast
  let p' := p.copy he₁ he₂
  have hs : p'.support=L := by simp [p',p]
  have hp : p'.IsPath := p'.isPath_def.mpr (hs ▸ hL)
  have hl : p'.length=d+1 := by
    have := p'.length_support
    rw [hs,hlen] at this
    omega
  refine ⟨hx,hy,?_,p',hp,hl,?_⟩
  · intro he
    have := (hp.nil_iff_eq.mpr he).length_eq_zero
    omega
  · simpa only [hs] using hint

def extNeighbors {V : Type*} (G : SimpleGraph V) (Q : Set V) (x : V) : Set V :=
  {u | G.Adj x u ∧ u ∉ Q}

def extClosed {V : Type*} (G : SimpleGraph V) (Q S : Set V) : Set V :=
  closedNeighborhood G S \ Q

 

theorem extClosed_disjoint {V : Type*} [Fintype V] {G : SimpleGraph V}
    {Q A B : Set V} (hQ : G.IsClique Q) (ht : 3 ≤ Q.ncard) (ht' : Q.ncard ≤ 4)
    (hcycle : ¬ SimpleGraph.cycleGraph 5 ⊑ G)
    (hA : A ⊆ Qᶜ) (hB : B ⊆ Qᶜ) (hAB : Disjoint A B)
    (hattach : ∀ u ∈ A, ∀ v ∈ B, ∃ x ∈ Q, ∃ y ∈ Q, x ≠ y ∧ G.Adj x u ∧ G.Adj y v) :
    Disjoint (extClosed G Q A) (extClosed G Q B) := by
  classical
  apply Set.disjoint_left.mpr
  intro z hzA hzB
  obtain ⟨u,hu,huz⟩ : ∃ u ∈ A, u=z ∨ G.Adj u z := by
    rcases hzA.1 with hu | ⟨u,hu,huz⟩
    · exact ⟨z,hu,Or.inl rfl⟩
    · exact ⟨u,hu,Or.inr huz⟩
  obtain ⟨v,hv,hvz⟩ : ∃ v ∈ B, v=z ∨ G.Adj v z := by
    rcases hzB.1 with hv | ⟨v,hv,hvz⟩
    · exact ⟨z,hv,Or.inl rfl⟩
    · exact ⟨v,hv,Or.inr hvz⟩
  have huv : u ≠ v := fun he => Set.disjoint_left.mp hAB hu (he ▸ hv)
  obtain ⟨x,hx,y,hy,hxy,hxu,hyv⟩ := hattach u hu v hv
  have hun := hA hu
  have hvn := hB hv
  have hz := hzA.2
  have hno2 := outsidePath_clique_forbidden hQ (k:=4) (by omega) ht' hcycle
    (x:=x) (y:=y) (d:=2) (by omega) (by omega)
  have hno3 := outsidePath_clique_forbidden hQ (k:=4) (by omega) ht' hcycle
    (x:=x) (y:=y) (d:=3) (by omega) (by omega)
  have hneq : ∀ w, w ∉ Q → w ≠ x ∧ w ≠ y := by
    intro w hw
    exact ⟨fun he => hw (he ▸ hx),fun he => hw (he ▸ hy)⟩
  have huq := hneq u hun
  have hvq := hneq v hvn
  have hzq := hneq z hz
  have hedge : ¬ G.Adj u v := by
    intro huvAdj
    apply hno2
    apply outsidePath_of_list [x,u,v,y]
    · simp [hxy,huq.2,hvq.2,Ne.symm huq.1,Ne.symm hvq.1,huv]
    · simpa using And.intro hxu (And.intro huvAdj hyv.symm)
    · rfl
    · rfl
    · rfl
    · exact hx
    · exact hy
    · intro w hw hwQ
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact (hun hwQ).elim
      · exact (hvn hwQ).elim
      · exact Or.inr rfl
  rcases huz with rfl | huz
  · rcases hvz with he | hvz
    · exact huv he.symm
    · exact hedge hvz.symm
  rcases hvz with rfl | hvz
  · exact hedge huz
  apply hno3
  apply outsidePath_of_list [x,u,z,v,y]
  · simp [hxy,huq.2,hvq.2,hzq.2,Ne.symm huq.1,
      Ne.symm hvq.1,Ne.symm hzq.1,huv,huz.ne,hvz.ne.symm]
  · simpa using And.intro hxu (And.intro huz (And.intro hvz.symm hyv.symm))
  · rfl
  · rfl
  · rfl
  · exact hx
  · exact hy
  · intro w hw hwQ
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact (hun hwQ).elim
    · exact (hz hwQ).elim
    · exact (hvn hwQ).elim
    · exact Or.inr rfl

 
structure Frame {V : Type*} (G : SimpleGraph V) (t : ℕ) where
  q : Fin t ↪ V
  adj : ∀ i j, i ≠ j → G.Adj (q i) (q j)

end CycleClique

end OAI
