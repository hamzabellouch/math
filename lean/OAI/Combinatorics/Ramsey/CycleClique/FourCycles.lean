import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.BallPacking
import OAI.Combinatorics.Ramsey.CycleClique.CachedDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateModel
import OAI.Combinatorics.Ramsey.CycleClique.CliqueBits
import OAI.Combinatorics.Ramsey.CycleClique.CompactDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CompactLabels
import OAI.Combinatorics.Ramsey.CycleClique.EdgeBits
import OAI.Combinatorics.Ramsey.CycleClique.EdgeDecisions
import OAI.Combinatorics.Ramsey.CycleClique.ExteriorFrames
import OAI.Combinatorics.Ramsey.CycleClique.FiniteGraphs
import OAI.Combinatorics.Ramsey.CycleClique.FrameProperties
import OAI.Combinatorics.Ramsey.CycleClique.Independence
import OAI.Combinatorics.Ramsey.CycleClique.IndependenceTwo
import OAI.Combinatorics.Ramsey.CycleClique.InducedGraphs
import OAI.Combinatorics.Ramsey.CycleClique.LabelDecisions
import OAI.Combinatorics.Ramsey.CycleClique.MatrixBits

namespace OAI

namespace CycleClique
open scoped SimpleGraph

namespace FourHyp
variable {V : Type*} [Fintype V] {G : SimpleGraph V} (H : FourHyp G)
include H

theorem U_two (T : Frame G 3) (i : Fin 3) : 2 ≤ (T.U i).ncard := by
  have := T.U_degree H.expansion i
  omega

theorem U_nonempty (T : Frame G 3) (i : Fin 3) : (T.U i).Nonempty :=
  (Set.ncard_pos).mp (lt_of_lt_of_le (by omega : 0<2) (H.U_two T i))

theorem disjoint_triangle (T : Frame G 3)
    (hdis : Pairwise (fun i j => Disjoint (T.U i) (T.U j))) :
    ∀ i, (T.U i).ncard=2 ∧ G.IsClique (T.U i) := by
  have hc := T.disjoint_U_closed H.cycle hdis
  have hb := extClosed_sum_bound T.U hc
  rw [T.cardQ,Fin.sum_univ_three] at hb
  have he := fun i => T.disjoint_U_expansion H.expansion hdis i (H.U_nonempty T i)
  have hi := fun i => independence_pos (G:=G) (H.U_nonempty T i)
  have he0 := he 0
  have he1 := he 1
  have he2 := he 2
  have hi0 := hi 0
  have hi1 := hi 1
  have hi2 := hi 2
  have ho := H.order
  intro i
  have hai : independence G (T.U i) ≤ 1 := by
    fin_cases i <;> dsimp at * <;> omega
  have hcli := clique_of_independence_le_one hai
  have hcu := T.clique_U_bound H.clique i hcli
  have hlo := H.U_two T i
  exact ⟨by omega,hcli⟩

 
theorem exists_overlap (T : Frame G 3) :
    ∃ S : Frame G 3, ∃ i j : Fin 3, i ≠ j ∧ (S.U i ∩ S.U j).Nonempty := by
  classical
  by_contra hn
  have hall : ∀ S : Frame G 3, Pairwise (fun i j => Disjoint (S.U i) (S.U j)) := by
    intro S i j hij
    apply Set.disjoint_left.mpr
    intro u hui huj
    exact hn ⟨S,i,j,hij,u,hui,huj⟩
  have hT := H.disjoint_triangle T (hall T)
  have hsix : ∀ i, 6 ≤ (extClosed G T.Q (T.U i)).ncard := by
    intro i
    obtain ⟨u,v,huv,hUi⟩ := Set.ncard_eq_two.mp (hT i).1
    have hu : u ∈ T.U i := by rw [hUi]; simp
    have hv : v ∈ T.U i := by rw [hUi]; simp
    let W := Frame.triangle hu.1 ((hT i).2 hu hv huv) hv.1.symm
    have hW1 := H.U_two W 1
    have hW2 := H.U_two W 2
    have hdis12 : Disjoint (W.U 1) (W.U 2) := hall W (by decide)
    have hdisU : Disjoint (T.U i) (W.U 1 ∪ W.U 2) := by
      apply Set.disjoint_left.mpr
      intro x hx hxW
      have hxQ : x ∈ W.Q := by
        rw [Frame.triangle_Q]
        rw [hUi] at hx
        simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx ⊢
        tauto
      rcases hxW with hxW | hxW <;> exact hxW.2 hxQ
    have hsub : T.U i ∪ (W.U 1 ∪ W.U 2) ⊆ extClosed G T.Q (T.U i) := by
      intro x hx
      rcases hx with hx | hx
      · exact ⟨Or.inl hx,hx.2⟩
      have hw : ∃ y ∈ T.U i, G.Adj y x ∧ x ∉ W.Q := by
        rcases hx with hx | hx
        · exact ⟨u,hu,hx.1,hx.2⟩
        · exact ⟨v,hv,hx.1,hx.2⟩
      obtain ⟨y,hy,hyx,hnW⟩ := hw
      refine ⟨Or.inr ⟨y,hy,hyx⟩,?_⟩
      intro hxQ
      have he : x=T.q i := T.boundary_U (hall T) i hy hxQ hyx
      subst x
      exact hnW (W.memQ 0)
    have hb := Set.ncard_le_ncard hsub
    rw [Set.ncard_union_eq hdisU,Set.ncard_union_eq hdis12,(hT i).1] at hb
    omega
  have hb := extClosed_sum_bound T.U (T.disjoint_U_closed H.cycle (hall T))
  rw [T.cardQ,Fin.sum_univ_three] at hb
  have h0 := hsix 0
  have h1 := hsix 1
  have h2 := hsix 2
  have ho := H.order
  omega

 
theorem closed_disjoint_of_U (T : Frame G 3) {A B : Set V} {i j : Fin 3}
    (hij : i ≠ j) (hA : A ⊆ T.U i) (hB : B ⊆ T.U j) (hdis : Disjoint A B) :
    Disjoint (extClosed G T.Q A) (extClosed G T.Q B) := by
  apply extClosed_disjoint T.clique (by rw [T.cardQ]) (by rw [T.cardQ]; omega) H.cycle
    (fun _ hu => (hA hu).2) (fun _ hv => (hB hv).2) hdis
  intro u hu v hv
  exact ⟨T.q i,T.memQ i,T.q j,T.memQ j,
    fun he => hij (T.q.injective he),(hA hu).1,(hB hv).1⟩

theorem no_exterior_adj (T : Frame G 3) {u v : V} {i j : Fin 3}
    (hij : i ≠ j) (hu : u ∈ T.U i) (hv : v ∈ T.U j) (huv : u ≠ v) :
    ¬ G.Adj u v := by
  have hd := H.closed_disjoint_of_U T hij (A:={u}) (B:={v})
    (by simpa) (by simpa) (by simp [huv])
  intro he
  exact Set.disjoint_left.mp hd (show v ∈ extClosed G T.Q {u} from
    ⟨Or.inr ⟨u,rfl,he⟩,hv.2⟩) ⟨Or.inl rfl,hv.2⟩

theorem no_triple (T : Frame G 3) {u : V}
    (h0 : u ∈ T.U 0) (h1 : u ∈ T.U 1) : u ∉ T.U 2 := by
  intro h2
  have hc : G.IsClique (insert u T.Q) := by
    have ha : ∀ x ∈ T.Q, G.Adj u x := by
      rintro x ⟨i,rfl⟩
      fin_cases i
      · exact h0.1.symm
      · exact h1.1.symm
      · exact h2.1.symm
    intro x hx y hy hxy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact (hxy rfl).elim
    · exact ha y hy
    · exact (ha x hx).symm
    · exact T.clique hx hy hxy
  have hb := (clique_ncard_le_cliqueNum hc).trans H.clique
  rw [Set.ncard_insert_of_notMem h0.2,T.cardQ] at hb
  omega

 
theorem overlap_cycle (T : Frame G 3) {i j l : Fin 3}
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) {u v : V}
    (hu : u ∈ T.U i ∩ T.U j) (hv : v ∈ T.U i ∩ T.U l) (huv : u ≠ v) : False := by
  have hnu := T.neQ hu.1.2
  have hnv := T.neQ hv.1.2
  apply H.cycle
  apply cycle_of_list [T.q j,u,T.q i,v,T.q l] (by simp)
  · simp [T.q.injective.eq_iff,hil,hjl,Ne.symm hij,hnu,hnv,
      Ne.symm (hnu j),Ne.symm (hnv j),Ne.symm (hnv i),huv]
  · simpa using And.intro hu.2.1 (And.intro hu.1.1.symm
      (And.intro hv.1.1 hv.2.1.symm))
  · simpa using T.adj l j hjl.symm

 
theorem overlap_disjoint_third (T : Frame G 3) (hne : (T.U 0 ∩ T.U 1).Nonempty) :
    Disjoint (T.U 0) (T.U 2) ∧ Disjoint (T.U 1) (T.U 2) := by
  obtain ⟨u,hu0,hu1⟩ := hne
  constructor
  · apply Set.disjoint_left.mpr
    intro v hv0 hv2
    have huv : u ≠ v := fun he => H.no_triple T hu0 hu1 (he ▸ hv2)
    exact H.overlap_cycle T (by decide : (0:Fin 3)≠1) (by decide) (by decide)
      ⟨hu0,hu1⟩ ⟨hv0,hv2⟩ huv
  · apply Set.disjoint_left.mpr
    intro v hv1 hv2
    have huv : u ≠ v := fun he => H.no_triple T hu0 hu1 (he ▸ hv2)
    exact H.overlap_cycle T (by decide : (1:Fin 3)≠0) (by decide) (by decide)
      ⟨hu1,hu0⟩ ⟨hv1,hv2⟩ huv

theorem overlap_independent (T : Frame G 3) : G.IsIndepSet (T.U 0 ∩ T.U 1) := by
  intro u hu v hv huv
  exact H.no_exterior_adj T (by decide : (0:Fin 3)≠1) hu.1 hv.2 huv

def overlapClasses (T : Frame G 3) : Fin 4 → Set V :=
  ![T.U 0 ∩ T.U 1,T.U 0 \ T.U 1,T.U 1 \ T.U 0,T.U 2]

theorem overlap_closed_pairwise (T : Frame G 3) (hne : (T.U 0 ∩ T.U 1).Nonempty) :
    Pairwise (fun i j => Disjoint (extClosed G T.Q (overlapClasses T i))
      (extClosed G T.Q (overlapClasses T j))) := by
  have hd := H.overlap_disjoint_third T hne
  have h01 := H.closed_disjoint_of_U T (by decide : (1:Fin 3)≠0)
    (A:=T.U 0 ∩ T.U 1) (B:=T.U 0 \ T.U 1) Set.inter_subset_right Set.sdiff_subset
    (Set.disjoint_left.mpr (by intro u hu hv; exact hv.2 hu.2))
  have h02 := H.closed_disjoint_of_U T (by decide : (0:Fin 3)≠1)
    (A:=T.U 0 ∩ T.U 1) (B:=T.U 1 \ T.U 0) Set.inter_subset_left Set.sdiff_subset
    (Set.disjoint_left.mpr (by intro u hu hv; exact hv.2 hu.1))
  have h03 := H.closed_disjoint_of_U T (by decide : (0:Fin 3)≠2)
    (A:=T.U 0 ∩ T.U 1) (B:=T.U 2) Set.inter_subset_left (Set.Subset.refl _)
    (hd.1.mono_left Set.inter_subset_left)
  have h12 := H.closed_disjoint_of_U T (by decide : (0:Fin 3)≠1)
    (A:=T.U 0 \ T.U 1) (B:=T.U 1 \ T.U 0) Set.sdiff_subset Set.sdiff_subset
    (Set.disjoint_left.mpr (by intro u hu hv; exact hu.2 hv.1))
  have h13 := H.closed_disjoint_of_U T (by decide : (0:Fin 3)≠2)
    (A:=T.U 0 \ T.U 1) (B:=T.U 2) Set.sdiff_subset (Set.Subset.refl _)
    (hd.1.mono_left Set.sdiff_subset)
  have h23 := H.closed_disjoint_of_U T (by decide : (1:Fin 3)≠2)
    (A:=T.U 1 \ T.U 0) (B:=T.U 2) Set.sdiff_subset (Set.Subset.refl _)
    (hd.2.mono_left Set.sdiff_subset)
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp only [overlapClasses] <;>
    first | exact (hij rfl).elim | assumption | exact h01.symm | exact h02.symm |
      exact h03.symm | exact h12.symm | exact h13.symm | exact h23.symm

 
theorem overlap_structure (T : Frame G 3) (hne : (T.U 0 ∩ T.U 1).Nonempty) :
    T.U 0 = T.U 1 ∧ (T.U 0).ncard=2 ∧ G.IsIndepSet (T.U 0) ∧
      (T.U 2).ncard=2 ∧ G.IsClique (T.U 2) := by
  have hd := H.overlap_disjoint_third T hne
  have hI := H.overlap_independent T
  have hbI : ∀ u ∈ T.U 0 ∩ T.U 1, ∀ x ∈ T.Q, G.Adj u x →
      x ∈ ({T.q 0,T.q 1} : Set V) := by
    rintro u hu x ⟨i,rfl⟩ hux
    fin_cases i
    · simp
    · simp
    · exact (H.no_triple T hu.1 hu.2 ⟨hux.symm,hu.1.2⟩).elim
  have hbA : ∀ u ∈ T.U 0 \ T.U 1, ∀ x ∈ T.Q, G.Adj u x →
      x ∈ ({T.q 0} : Set V) := by
    rintro u hu x ⟨i,rfl⟩ hux
    fin_cases i
    · rfl
    · exact (hu.2 ⟨hux.symm,hu.1.2⟩).elim
    · exact (Set.disjoint_left.mp hd.1 hu.1 ⟨hux.symm,hu.1.2⟩).elim
  have hbB : ∀ u ∈ T.U 1 \ T.U 0, ∀ x ∈ T.Q, G.Adj u x →
      x ∈ ({T.q 1} : Set V) := by
    rintro u hu x ⟨i,rfl⟩ hux
    fin_cases i
    · exact (hu.2 ⟨hux.symm,hu.1.2⟩).elim
    · rfl
    · exact (Set.disjoint_left.mp hd.2 hu.1 ⟨hux.symm,hu.1.2⟩).elim
  have hbD : ∀ u ∈ T.U 2, ∀ x ∈ T.Q, G.Adj u x →
      x ∈ ({T.q 2} : Set V) := by
    rintro u hu x ⟨i,rfl⟩ hux
    fin_cases i
    · exact (Set.disjoint_left.mp hd.1 ⟨hux.symm,hu.2⟩ hu).elim
    · exact (Set.disjoint_left.mp hd.2 ⟨hux.symm,hu.2⟩ hu).elim
    · rfl
  have heI := extClosed_indep_expansion H.expansion hI (fun _ hu => hu.1.2) hne hbI
  have hcPair : ({T.q 0,T.q 1} : Set V).ncard=2 := by
    simp [T.q.injective.eq_iff]
  rw [hcPair] at heI
  have heA : (T.U 0 \ T.U 1).Nonempty →
      4 ≤ (extClosed G T.Q (T.U 0 \ T.U 1)).ncard := by
    intro hn
    have hh := extClosed_expansion H.expansion (fun _ hu => hu.1.2) hn hbA
    have hi := independence_pos (G:=G) hn
    simp only [Set.ncard_singleton] at hh
    omega
  have heB : (T.U 1 \ T.U 0).Nonempty →
      4 ≤ (extClosed G T.Q (T.U 1 \ T.U 0)).ncard := by
    intro hn
    have hh := extClosed_expansion H.expansion (fun _ hu => hu.1.2) hn hbB
    have hi := independence_pos (G:=G) hn
    simp only [Set.ncard_singleton] at hh
    omega
  have heD := extClosed_expansion H.expansion (T.exterior 2) (H.U_nonempty T 2) hbD
  simp only [Set.ncard_singleton] at heD
  have hiD := independence_pos (G:=G) (H.U_nonempty T 2)
  have hs := extClosed_sum_bound (overlapClasses T) (H.overlap_closed_pairwise T hne)
  rw [T.cardQ,Fin.sum_univ_four] at hs
  dsimp [overlapClasses] at hs
  have ho := H.order
  have hr := (Set.ncard_pos).mpr hne
  have hU0 := H.U_two T 0
  have hU1 := H.U_two T 1
  have hr2 : (T.U 0 ∩ T.U 1).ncard=2 := by
    have hrne : (T.U 0 ∩ T.U 1).ncard≠1 := by
      intro he
      have hA : (T.U 0 \ T.U 1).Nonempty := by
        by_contra hn
        have hsub : T.U 0 ⊆ T.U 0 ∩ T.U 1 := by
          intro u hu
          refine ⟨hu,?_⟩
          by_contra hh
          exact hn ⟨u,hu,hh⟩
        have := Set.ncard_le_ncard hsub
        omega
      have hB : (T.U 1 \ T.U 0).Nonempty := by
        by_contra hn
        have hsub : T.U 1 ⊆ T.U 0 ∩ T.U 1 := by
          intro u hu
          refine ⟨?_,hu⟩
          by_contra hh
          exact hn ⟨u,hu,hh⟩
        have := Set.ncard_le_ncard hsub
        omega
      have := heA hA
      have := heB hB
      omega
    omega
  have hA0 : (T.U 0 \ T.U 1)=∅ := by
    apply Set.not_nonempty_iff_eq_empty.mp
    intro hn
    have := heA hn
    omega
  have hB0 : (T.U 1 \ T.U 0)=∅ := by
    apply Set.not_nonempty_iff_eq_empty.mp
    intro hn
    have := heB hn
    omega
  have hEq : T.U 0=T.U 1 := Set.Subset.antisymm (Set.sdiff_eq_empty.mp hA0)
    (Set.sdiff_eq_empty.mp hB0)
  have hIe : T.U 0 ∩ T.U 1=T.U 0 := by rw [← hEq,Set.inter_self]
  have hDcl := clique_of_independence_le_one (G:=G) (S:=T.U 2) (by omega)
  have hDmax := T.clique_U_bound H.clique 2 hDcl
  have hDmin := H.U_two T 2
  exact ⟨hEq,by simpa only [hIe] using hr2,by simpa only [hIe] using hI,
    by omega,hDcl⟩

 

theorem overlap_vertex_degree (T : Frame G 3) (hne : (T.U 0 ∩ T.U 1).Nonempty)
    {w : V} (hw : w ∈ T.U 0) : (extNeighbors G T.Q w).ncard ≤ 2 := by
  have hs := H.overlap_structure T hne
  have hw1 : w ∈ T.U 1 := hs.1 ▸ hw
  let S := Frame.triangle (T.adj 0 1 (by decide)) hw1.1 hw.1.symm
  have hq2 : T.q 2 ∉ S.Q := by
    rw [Frame.triangle_Q]
    simp [T.q.injective.eq_iff,Ne.symm (T.neQ hw.2 2)]
  have hov : (S.U 0 ∩ S.U 1).Nonempty :=
    ⟨T.q 2,⟨T.adj 0 2 (by decide),hq2⟩,⟨T.adj 1 2 (by decide),hq2⟩⟩
  have hSc := (H.overlap_structure S hov).2.2.2.1
  have hsub : extNeighbors G T.Q w ⊆ S.U 2 := by
    intro x hx
    refine ⟨hx.1,?_⟩
    rw [Frame.triangle_Q]
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
    rintro (rfl | rfl | rfl)
    · exact hx.2 (T.memQ 0)
    · exact hx.2 (T.memQ 1)
    · exact hx.1.ne rfl
  exact (Set.ncard_le_ncard hsub).trans_eq hSc

 
theorem overlap_contradiction (T : Frame G 3) (hne : (T.U 0 ∩ T.U 1).Nonempty) : False := by
  have hs := H.overlap_structure T hne
  obtain ⟨w,z,hwz,hU⟩ := Set.ncard_eq_two.mp hs.2.1
  have hw : w ∈ T.U 0 := by rw [hU]; simp
  have hz : z ∈ T.U 0 := by rw [hU]; simp
  have hdw := H.overlap_vertex_degree T hne hw
  have hdz := H.overlap_vertex_degree T hne hz
  have hsub : extClosed G T.Q (T.U 0) ⊆
      T.U 0 ∪ (extNeighbors G T.Q w ∪ extNeighbors G T.Q z) := by
    intro x hx
    rcases hx.1 with hxI | ⟨u,hu,hux⟩
    · exact Or.inl hxI
    · rw [hU] at hu
      rcases hu with rfl | rfl
      · exact Or.inr (Or.inl ⟨hux,hx.2⟩)
      · exact Or.inr (Or.inr ⟨hux,hx.2⟩)
  have hb := (Set.ncard_le_ncard hsub).trans (Set.ncard_union_le _ _)
  have hb' := Set.ncard_union_le (extNeighbors G T.Q w) (extNeighbors G T.Q z)
  have hboundary : ∀ u ∈ T.U 0, ∀ x ∈ T.Q, G.Adj u x →
      x ∈ ({T.q 0,T.q 1} : Set V) := by
    rintro u hu x ⟨i,rfl⟩ hux
    fin_cases i
    · simp
    · simp
    · exact (H.no_triple T hu (hs.1 ▸ hu) ⟨hux.symm,hu.2⟩).elim
  have he := extClosed_indep_expansion H.expansion hs.2.2.1 (T.exterior 0)
    (H.U_nonempty T 0) hboundary
  have hc2 : ({T.q 0,T.q 1} : Set V).ncard=2 := by simp [T.q.injective.eq_iff]
  rw [hc2,hs.2.1] at he
  rw [hs.2.1] at hb
  omega

 
theorem contradiction (T : Frame G 3) : False := by
  obtain ⟨S,i,j,hij,hne⟩ := H.exists_overlap T
  let e : Fin 3 ≃ Fin 3 := (Equiv.swap 1 ((Equiv.swap 0 i) j)).trans (Equiv.swap 0 i)
  have he0 : e 0=i := by
    fin_cases i <;> fin_cases j <;> simp_all [e,Equiv.swap_apply_def]
  have he1 : e 1=j := by
    fin_cases i <;> fin_cases j <;> simp_all [e,Equiv.swap_apply_def]
  apply H.overlap_contradiction (S.reindex e)
  simpa only [Frame.reindex_U,he0,he1] using hne

end FourHyp

end CycleClique

end OAI
