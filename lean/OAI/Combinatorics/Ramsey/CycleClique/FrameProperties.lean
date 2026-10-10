import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.BallPacking
import OAI.Combinatorics.Ramsey.CycleClique.Basic
import OAI.Combinatorics.Ramsey.CycleClique.CachedDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateModel
import OAI.Combinatorics.Ramsey.CycleClique.CliqueBits
import OAI.Combinatorics.Ramsey.CycleClique.CompactDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CompactLabels
import OAI.Combinatorics.Ramsey.CycleClique.DenseCycles
import OAI.Combinatorics.Ramsey.CycleClique.DistanceLayers
import OAI.Combinatorics.Ramsey.CycleClique.EdgeBits
import OAI.Combinatorics.Ramsey.CycleClique.EdgeDecisions
import OAI.Combinatorics.Ramsey.CycleClique.ExteriorBalls
import OAI.Combinatorics.Ramsey.CycleClique.ExteriorFrames
import OAI.Combinatorics.Ramsey.CycleClique.ExteriorPaths
import OAI.Combinatorics.Ramsey.CycleClique.FiniteGraphs
import OAI.Combinatorics.Ramsey.CycleClique.Independence
import OAI.Combinatorics.Ramsey.CycleClique.IndependenceTwo
import OAI.Combinatorics.Ramsey.CycleClique.LabelDecisions
import OAI.Combinatorics.Ramsey.CycleClique.MatrixBits

namespace OAI

namespace CycleClique
open scoped SimpleGraph

namespace Frame
variable {V : Type*} {G : SimpleGraph V} {t : ℕ} (T : Frame G t)

def Q : Set V := Set.range T.q

def U (i : Fin t) : Set V := extNeighbors G T.Q (T.q i)

theorem memQ (i : Fin t) : T.q i ∈ T.Q := ⟨i,rfl⟩

theorem cardQ [Fintype V] : T.Q.ncard=t := by
  rw [Q,Set.ncard_range_of_injective T.q.injective]
  simp

theorem clique : G.IsClique T.Q := by
  rintro x ⟨i,rfl⟩ y ⟨j,rfl⟩ hxy
  exact T.adj i j (fun he => hxy (congrArg T.q he))

theorem exterior (i : Fin t) : T.U i ⊆ T.Qᶜ := fun _ hu => hu.2

theorem neQ {u : V} (hu : u ∉ T.Q) (i : Fin t) : u ≠ T.q i :=
  fun he => hu (he ▸ T.memQ i)

def reindex (e : Fin t ≃ Fin t) : Frame G t where
  q := e.toEmbedding.trans T.q
  adj i j hij := T.adj (e i) (e j) (fun he => hij (e.injective he))

theorem reindex_Q (e : Fin t ≃ Fin t) : (T.reindex e).Q=T.Q := by
  ext u
  constructor
  · rintro ⟨i,rfl⟩
    exact T.memQ _
  · rintro ⟨i,rfl⟩
    exact ⟨e.symm i, by simp [reindex]⟩

theorem reindex_U (e : Fin t ≃ Fin t) (i : Fin t) :
    (T.reindex e).U i=T.U (e i) := by
  simp only [U,reindex_Q]
  rfl

 
def triangle {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a) : Frame G 3 where
  q := ⟨![a,b,c], by
    intro i j he
    fin_cases i <;> fin_cases j <;> aesop⟩
  adj i j hij := by
    change G.Adj (![a,b,c] i) (![a,b,c] j)
    fin_cases i <;> fin_cases j <;> simp_all [SimpleGraph.adj_comm]

theorem triangle_Q {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a) :
    (triangle hab hbc hca).Q={a,b,c} := by
  ext u
  simp only [Q,Set.mem_range,Set.mem_insert_iff,Set.mem_singleton_iff]
  constructor
  · rintro ⟨i,rfl⟩
    change ![a,b,c] i = a ∨ ![a,b,c] i = b ∨ ![a,b,c] i = c
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl)
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩

end Frame

theorem exists_frame {V : Type*} [Fintype V] {G : SimpleGraph V} {t : ℕ}
    (ht : t ≤ G.cliqueNum) : Nonempty (Frame G t) := by
  obtain ⟨f⟩ := (complete_isContained_iff_le_cliqueNum G t).mpr ht
  refine ⟨⟨f.toEmbedding,?_⟩⟩
  intro i j hij
  exact f.toHom.map_adj (by simpa using hij)

 
theorem extClosed_sum_bound {V ι : Type*} [Fintype V] [Fintype ι]
    {G : SimpleGraph V} {Q : Set V} (S : ι → Set V)
    (hdis : Pairwise (fun i j => Disjoint (extClosed G Q (S i)) (extClosed G Q (S j)))) :
    Q.ncard + ∑ i, (extClosed G Q (S i)).ncard ≤ Fintype.card V := by
  classical
  have hc := ncard_union_layers (fun i => extClosed G Q (S i)) hdis Finset.univ
  have hb := Set.ncard_le_ncard (show (⋃ i ∈ Finset.univ,extClosed G Q (S i)) ⊆ Qᶜ from by
    rintro v hv
    obtain ⟨i,_,hi⟩ := Set.mem_iUnion₂.mp hv
    exact hi.2)
  have he := Set.ncard_add_ncard_compl Q
  rw [Nat.card_eq_fintype_card] at he
  omega

theorem extClosed_pair_bound {V : Type*} [Fintype V] {G : SimpleGraph V}
    {Q A B : Set V} (h : Disjoint (extClosed G Q A) (extClosed G Q B)) :
    Q.ncard + (extClosed G Q A).ncard + (extClosed G Q B).ncard ≤ Fintype.card V := by
  have hb := Set.ncard_le_ncard (show extClosed G Q A ∪ extClosed G Q B ⊆ Qᶜ from by
    rintro x (h | h) <;> exact h.2)
  rw [Set.ncard_union_eq h] at hb
  have he := Set.ncard_add_ncard_compl Q
  rw [Nat.card_eq_fintype_card] at he
  omega

 
theorem extClosed_expansion {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} (hexp : ∀ I, G.IsIndepSet I → I.Nonempty →
      k * I.ncard+1 ≤ (closedNeighborhood G I).ncard)
    {Q S R : Set V} (hS : S ⊆ Qᶜ) (hne : S.Nonempty)
    (hb : ∀ u ∈ S, ∀ x ∈ Q, G.Adj u x → x ∈ R) :
    k * independence G S + 1 ≤ (extClosed G Q S).ncard + R.ncard := by
  obtain ⟨I,hIS,hI,hIc⟩ := exists_indep_of_independence G S
  have hi := independence_pos (G:=G) hne
  have he := hexp I hI ((Set.ncard_pos).mp (by omega))
  have hs : closedNeighborhood G I ⊆ extClosed G Q S ∪ R := by
    intro x hx
    by_cases hxQ : x ∈ Q
    · right
      rcases hx with hx | ⟨u,hu,hux⟩
      · exact (hS (hIS hx) hxQ).elim
      · exact hb u (hIS hu) x hxQ hux
    · left
      exact ⟨closedNeighborhood_mono G hIS hx,hxQ⟩
  have hc := (Set.ncard_le_ncard hs).trans (Set.ncard_union_le _ _)
  rw [hIc] at he
  omega

theorem extClosed_indep_expansion {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} (hexp : ∀ I, G.IsIndepSet I → I.Nonempty →
      k * I.ncard+1 ≤ (closedNeighborhood G I).ncard)
    {Q I R : Set V} (hI : G.IsIndepSet I) (hS : I ⊆ Qᶜ) (hne : I.Nonempty)
    (hb : ∀ u ∈ I, ∀ x ∈ Q, G.Adj u x → x ∈ R) :
    k * I.ncard + 1 ≤ (extClosed G Q I).ncard + R.ncard := by
  have hi := indep_ncard_le_independence hI (Set.Subset.refl I)
  exact (by gcongr : k*I.ncard+1 ≤ k*independence G I+1).trans
    (extClosed_expansion hexp hS hne hb)

theorem Frame.U_degree {V : Type*} [Fintype V] {G : SimpleGraph V} {k t : ℕ}
    (T : Frame G t) (hexp : ∀ I, G.IsIndepSet I → I.Nonempty →
      k * I.ncard+1 ≤ (closedNeighborhood G I).ncard) (i : Fin t) :
    k+1 ≤ t+(T.U i).ncard := by
  have he := hexp {T.q i} (Set.pairwise_singleton _ _) (Set.singleton_nonempty _)
  have hs : closedNeighborhood G {T.q i} ⊆ T.Q ∪ T.U i := by
    rintro x (rfl | ⟨y,hy,hyx⟩)
    · exact Or.inl (T.memQ i)
    · have he : y=T.q i := hy
      subst y
      by_cases hx : x ∈ T.Q
      · exact Or.inl hx
      · exact Or.inr ⟨hyx,hx⟩
  have hc := (Set.ncard_le_ncard hs).trans (Set.ncard_union_le _ _)
  rw [T.cardQ] at hc
  simp only [Set.ncard_singleton,Nat.mul_one] at he
  omega

theorem Frame.clique_U_bound {V : Type*} [Fintype V] {G : SimpleGraph V} {t u : ℕ}
    (T : Frame G t) (hcl : G.cliqueNum ≤ u) (i : Fin t) (hUi : G.IsClique (T.U i)) :
    (T.U i).ncard+1 ≤ u := by
  have hC : G.IsClique (insert (T.q i) (T.U i)) := by
    intro x hx y hy hxy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact (hxy rfl).elim
    · exact hy.1
    · exact hx.1.symm
    · exact hUi hx hy hxy
  have hc := (clique_ncard_le_cliqueNum hC).trans hcl
  rwa [Set.ncard_insert_of_notMem (fun hh => hh.2 (T.memQ i))] at hc

theorem Frame.U_ball {V : Type*} {G : SimpleGraph V} {t : ℕ}
    (T : Frame G t) (i : Fin t) : T.U i=outsideBall G T.Q (T.q i) 0 := rfl

theorem Frame.extClosed_U_ball {V : Type*} {G : SimpleGraph V} {t : ℕ}
    (T : Frame G t) (i : Fin t) : extClosed G T.Q (T.U i)=outsideBall G T.Q (T.q i) 1 := by
  ext x
  simp only [extClosed,closedNeighborhood,Set.mem_sdiff,Set.mem_union,Set.mem_ofPred_eq,
    outsideBall,Frame.U,extNeighbors]
  tauto

theorem Frame.boundary_U {V : Type*} {G : SimpleGraph V} {t : ℕ}
    (T : Frame G t) (hdis : Pairwise (fun i j => Disjoint (T.U i) (T.U j)))
    (i : Fin t) {u x : V} (hu : u ∈ T.U i) (hx : x ∈ T.Q) (hux : G.Adj u x) :
    x ∈ ({T.q i} : Set V) := by
  obtain ⟨j,rfl⟩ := hx
  have hj : j=i := by
    by_contra hji
    exact Set.disjoint_left.mp (hdis hji) (show u ∈ T.U j from ⟨hux.symm,hu.2⟩) hu
  subst j
  rfl

theorem Frame.disjoint_U_expansion {V : Type*} [Fintype V] {G : SimpleGraph V} {k t : ℕ}
    (T : Frame G t) (hexp : ∀ I, G.IsIndepSet I → I.Nonempty →
      k*I.ncard+1 ≤ (closedNeighborhood G I).ncard)
    (hdis : Pairwise (fun i j => Disjoint (T.U i) (T.U j)))
    (i : Fin t) (hne : (T.U i).Nonempty) :
    k * independence G (T.U i) ≤ (extClosed G T.Q (T.U i)).ncard := by
  have hh := extClosed_expansion hexp (T.exterior i) hne (R:={T.q i})
    (fun _ hu _ hx hux => T.boundary_U hdis i hu hx hux)
  simp only [Set.ncard_singleton] at hh
  omega

theorem Frame.disjoint_U_closed {V : Type*} [Fintype V] {G : SimpleGraph V}
    (T : Frame G 3) (hcycle : ¬ SimpleGraph.cycleGraph 5 ⊑ G)
    (hdis : Pairwise (fun i j => Disjoint (T.U i) (T.U j))) :
    Pairwise (fun i j => Disjoint (extClosed G T.Q (T.U i)) (extClosed G T.Q (T.U j))) := by
  intro i j hij
  apply extClosed_disjoint T.clique (by rw [T.cardQ]) (by rw [T.cardQ]; omega) hcycle
    (T.exterior i) (T.exterior j) (hdis hij)
  intro u hu v hv
  exact ⟨T.q i,T.memQ i,T.q j,T.memQ j,fun he => hij (T.q.injective he),hu.1,hv.1⟩

 

theorem small_four_clique {V : Type*} [Fintype V] {G : SimpleGraph V}
    (horder : Fintype.card V ≤ 17) (hcycle : ¬ SimpleGraph.cycleGraph 5 ⊑ G)
    (hexp : ∀ I, G.IsIndepSet I → I.Nonempty → 4*I.ncard+1 ≤ (closedNeighborhood G I).ncard)
    (T : Frame G 4) : False := by
  have hno : ∀ i j : Fin 4, i ≠ j → ∀ d, 1 ≤ d → d ≤ 3 →
      ¬ OutsidePath G T.Q (T.q i) (T.q j) d := by
    intro i j hij d hd hd'
    exact outsidePath_clique_forbidden T.clique (by omega) (by rw [T.cardQ]) hcycle
      (by rw [T.cardQ]; omega) (by omega)
  have hdis : Pairwise (fun i j => Disjoint (T.U i) (T.U j)) := by
    intro i j hij
    rw [T.U_ball,T.U_ball]
    exact (outside_balls_separated (T.memQ i) (T.memQ j)
      (fun he => hij (T.q.injective he)) (fun d hd hd' => hno i j hij d hd (by omega))).1
  have hclosed : Pairwise (fun i j => Disjoint (extClosed G T.Q (T.U i))
      (extClosed G T.Q (T.U j))) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro z hzi hzj
    rw [T.extClosed_U_ball] at hzi hzj
    obtain ⟨d,hd,hd',hp⟩ := outsidePath_of_balls_meet (T.memQ i) (T.memQ j)
      (fun he => hij (T.q.injective he)) hzi hzj
    exact hno i j hij d hd hd' hp
  have hb : ∀ i : Fin 4, 4 ≤ (extClosed G T.Q (T.U i)).ncard := by
    intro i
    have hu := T.U_degree hexp i
    have hne : (T.U i).Nonempty := (Set.ncard_pos).mp (by omega)
    have hi := independence_pos (G:=G) hne
    have he := T.disjoint_U_expansion hexp hdis i hne
    omega
  have hs := extClosed_sum_bound T.U hclosed
  rw [T.cardQ] at hs
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hb i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hh
  omega

 
structure FourHyp {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop where
  order : Fintype.card V ≤ 17
  cycle : ¬ SimpleGraph.cycleGraph 5 ⊑ G
  clique : G.cliqueNum ≤ 3
  expansion : ∀ I, G.IsIndepSet I → I.Nonempty → 4*I.ncard+1 ≤ (closedNeighborhood G I).ncard

end CycleClique

end OAI
