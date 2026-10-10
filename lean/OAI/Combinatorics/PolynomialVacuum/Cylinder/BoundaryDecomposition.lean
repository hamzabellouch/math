import OAI.Combinatorics.PolynomialVacuum.Cylinder.ArcRemoval

namespace OAI

namespace PolynomialVacuumCylinder
open Classical
variable {M : ℕ}

 
structure BoundaryArc (D : Finset (Vertex M)) where
  start : Germ M
  word : List Bool
  nonempty : word≠[]
  startInside : start.1∈D
  startOutside : (reverseGerm start).1∉D
  distinct : (traced start word).Nodup
  inside : ∀v∈traced start word,v∈D
  endOutside : (terminalGerm start word).1∉D
  endInside : (reverseGerm (terminalGerm start word)).1∈D

namespace BoundaryArc
noncomputable def vertices {D : Finset (Vertex M)} (A : BoundaryArc D) : Finset (Vertex M) :=
  (traced A.start A.word).toFinset
noncomputable def current {D : Finset (Vertex M)} (A : BoundaryArc D) : Edge M →₀ ℤ :=
  arcFlow A.start A.word
end BoundaryArc

namespace OpenIce
variable (D : Finset (Vertex M)) (q : Edge M →₀ ℤ) (hq : ∀v∈D,LocalIce q v)

noncomputable def boundaryArc (a : activeInside D q) (ha : (network D q hq).Source a) : BoundaryArc D where
  start := (a.val,enter D q hq a)
  word := (network D q hq).pathWord a ha
  nonempty := by
    intro hh
    have hl:=congrArg List.length hh
    simp only [OpenNetwork.pathWord,List.length_ofFn,List.length_nil] at hl
    have hp:=(network D q hq).pathLength_pos a ha
    omega
  startInside := (Finset.mem_inter.mp a.property).2
  startOutside := enter_outside_domain D q hq a ha
  distinct := (network D q hq).pathWord_nodup a ha
  inside := fun _ hv => (Finset.mem_inter.mp ((network D q hq).pathWord_inside a ha hv)).2
  endOutside := by
    have ht : terminalGerm (a.val,enter D q hq a) ((network D q hq).pathWord a ha)=
        (network D q hq).pathEnd a ha := (network D q hq).pathWord_terminal a ha
    rw [ht]
    apply exit_outside_domain D q hq
    apply (network D q hq).pathSite_exit a ha ((network D q hq).pathLast a ha)
    change (network D q hq).pathLength a ha-1+1=(network D q hq).pathLength a ha
    have := (network D q hq).pathLength_pos a ha
    omega
  endInside := by
    have ht : terminalGerm (a.val,enter D q hq a) ((network D q hq).pathWord a ha)=
        (network D q hq).pathEnd a ha := (network D q hq).pathWord_terminal a ha
    rw [ht]
    simp only [reverseGerm,OpenNetwork.pathEnd,neighbor_neighbor]
    exact (Finset.mem_inter.mp (((network D q hq).pathSite a ha ((network D q hq).pathLast a ha)).property)).2

@[simp] theorem boundaryArc_vertices (a : activeInside D q) (ha : (network D q hq).Source a) :
    (boundaryArc D q hq a ha).vertices=pathVertices D q hq a ha := rfl
@[simp] theorem boundaryArc_current (a : activeInside D q) (ha : (network D q hq).Source a) :
    (boundaryArc D q hq a ha).current=extractedArc D q hq a ha := rfl
end OpenIce

 

structure BoundaryDecomposition (D : Finset (Vertex M)) (q : Edge M →₀ ℤ) where
  arcs : List (BoundaryArc D)
  closed : Edge M →₀ ℤ
  reconstruction : q=(arcs.map BoundaryArc.current).sum+closed
  ice : ∀v,LocalIce closed v
  contained : activeSites closed⊆D
  pairwise : arcs.Pairwise (fun A B => Disjoint A.vertices B.vertices)
  disjoint_closed : ∀A∈arcs,Disjoint A.vertices (activeSites closed)
  arcs_active : ∀A∈arcs,A.vertices⊆activeInside D q
  closed_active : activeSites closed⊆activeInside D q

 

theorem boundary_decomposition (D : Finset (Vertex M)) (q : Edge M →₀ ℤ)
    (hq : ∀v∈D,LocalIce q v) (hs : SupportedAt D q) : Nonempty (BoundaryDecomposition D q) := by
  have main : ∀n : ℕ,∀q : Edge M →₀ ℤ,(activeInside D q).card=n →
      (∀v∈D,LocalIce q v) → SupportedAt D q → Nonempty (BoundaryDecomposition D q) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro q hn hq hs
      by_cases he : ∃a : activeInside D q,(OpenIce.network D q hq).Source a
      · obtain ⟨a,ha⟩:=he
        let A:=OpenIce.boundaryArc D q hq a ha
        let r:=q-OpenIce.extractedArc D q hq a ha
        have hlt : (activeInside D r).card<n := by
          rw [← hn]
          exact OpenIce.residual_card_lt D q hq a ha
        obtain ⟨B⟩:=ih (activeInside D r).card hlt r rfl
          (OpenIce.remove_arc_ice D q hq a ha) (OpenIce.residual_supported D q hq hs a ha)
        have hr : activeInside D r=activeInside D q\A.vertices :=
          OpenIce.residual_active D q hq a ha
        have hss : activeInside D r⊆activeInside D q := by rw [hr]; exact Finset.sdiff_subset
        have hd : Disjoint A.vertices (activeInside D r) := by
          rw [hr]
          exact Finset.disjoint_left.mpr (fun _ ha hb => (Finset.mem_sdiff.mp hb).2 ha)
        refine ⟨{
          arcs := A::B.arcs
          closed := B.closed
          reconstruction := ?_
          ice := B.ice
          contained := B.contained
          pairwise := ?_
          disjoint_closed := ?_
          arcs_active := ?_
          closed_active := B.closed_active.trans hss
        }⟩
        · simp only [List.map_cons,List.sum_cons]
          have hb:=B.reconstruction
          change q-OpenIce.extractedArc D q hq a ha=_ at hb
          change q=OpenIce.extractedArc D q hq a ha+_+_
          rw [sub_eq_iff_eq_add] at hb
          exact hb.trans (by abel)
        · apply List.pairwise_cons.mpr
          refine ⟨?_,B.pairwise⟩
          intro C hC
          exact hd.mono_right (B.arcs_active C hC)
        · intro C hC
          rcases List.mem_cons.mp hC with rfl | hC
          · exact hd.mono_right B.closed_active
          · exact B.disjoint_closed C hC
        · intro C hC
          rcases List.mem_cons.mp hC with rfl | hC
          · exact OpenIce.pathVertices_subset D q hq a ha
          · exact (B.arcs_active C hC).trans hss
      · have hall : ∀a : activeInside D q,¬(OpenIce.network D q hq).Source a := fun a ha => he ⟨a,ha⟩
        have hin:=OpenIce.no_source_active_subset D q hq hs hall
        exact ⟨{
          arcs := []
          closed := q
          reconstruction := by simp
          ice := OpenIce.no_source_global_ice D q hq hs hall
          contained := hin
          pairwise := by simp
          disjoint_closed := by simp
          arcs_active := by simp
          closed_active := fun _ hv => Finset.mem_inter.mpr ⟨hv,hin hv⟩
        }⟩
  exact main _ q rfl hq hs

end PolynomialVacuumCylinder

end OAI
