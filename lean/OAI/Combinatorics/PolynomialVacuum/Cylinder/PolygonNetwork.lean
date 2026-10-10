import OAI.Combinatorics.PolynomialVacuum.Cylinder.TwoOrientations
import OAI.Combinatorics.PolynomialVacuum.Geometry.PolygonOrientationAssembly

namespace OAI

namespace PolynomialVacuumCylinder
open Classical
variable {M : ℕ}
namespace ClosedNetwork
variable (C : ClosedNetwork M)

theorem polygon_edges_subset_flow (v : C.sites) : (C.polygon v).val⊆C.flow.support := by
  intro e he
  obtain ⟨u,_,hu⟩:=(C.mem_polygon_edges v e).mp he
  have h := C.oriented_flow_at u (C.exit u)
  simp only [ite_true,ite_eq_right (C.distinct u).symm,sub_zero] at h
  apply Finsupp.mem_support_iff.mpr
  intro hz
  have hh : orientedFlow C.flow (u.val,C.exit u)=0 := by
    apply (orientedFlow_eq_zero_iff _ _).mpr
    change edgeOf (u.val,C.exit u)=e at hu
    rw [hu]
    exact hz
  omega
end ClosedNetwork

namespace IceNetwork
variable (q : Edge M →₀ ℤ) (hq : ∀ v,LocalIce q v)
include hq

private theorem exit_of_contour (g : Germ M) (b : Bool) (h : LocalContour q g b)
    (v : activeSites q) (hv : v.val=g.1) : exit q hq v=outgoingSlot g b := by
  apply exit_of_pos
  rw [hv,h]
  simp [outgoingSlot_ne g b]

private theorem enter_of_contour (g : Germ M) (b : Bool) (h : LocalContour q g b)
    (v : activeSites q) (hv : v.val=g.1) : enter q hq v=g.2 := by
  apply enter_of_neg
  rw [hv,h]
  simp [Ne.symm (outgoingSlot_ne g b)]

theorem contour_edges_in_cycle (root : (network q hq).sites) (g : Germ M) (w : List Bool)
    (hc : WordContour q g w) (v : (network q hq).sites) (hv : v.val=g.1)
    (hr : (network q hq).next.SameCycle root v) :
    tracedEdges g w⊆((network q hq).polygon root).val := by
  induction w generalizing g v with
  | nil => simp [tracedEdges]
  | cons b w ih =>
    have ho := exit_of_contour q hq g b hc.1 v hv
    change (network q hq).exit v=outgoingSlot g b at ho
    have hm : ((network q hq).next v).val=(advance g b).1 := by
      rw [← (network q hq).incident,ho,hv]
      rfl
    intro e he
    rcases Finset.mem_insert.mp he with he | he
    · subst e
      apply ((network q hq).mem_polygon_edges root _).mpr
      refine ⟨v,((network q hq).mem_polygon_vertices root v).mpr hr,?_⟩
      change edgeOf (v.val,(network q hq).exit v)=edgeOf (g.1,outgoingSlot g b)
      rw [hv,ho]
    · apply ih (advance g b) hc.2 ((network q hq).next v) hm ?_ he
      exact hr.apply_right

 

theorem polygon_of_word (g : Germ M) (w : List Bool) (hw : w≠[])
    (hN : (traced g w).Nodup) (hc : terminalGerm g w=g) (he : wordFlow g w=q) :
    ∃ v : (network q hq).sites,
      ((network q hq).polygon v).val=tracedEdges g w ∧
      (network q hq).componentFlow ((network q hq).polygon v)=q := by
  have hcont : WordContour q g w := he ▸ simple_closed_word_contour g w hN hc
  have hg : g.1∈activeSites q := by
    obtain ⟨b,u,rfl⟩:=List.exists_cons_of_ne_nil hw
    refine (mem_activeSites q g.1).mpr ⟨g.2,?_⟩
    rw [hcont.1]
    simp [Ne.symm (outgoingSlot_ne g b)]
  let v : (network q hq).sites:=⟨g.1,hg⟩
  have hs : q.support=tracedEdges g w := by rw [← he,simple_word_support _ _ hN hc]
  have hp : ((network q hq).polygon v).val=tracedEdges g w := by
    apply Finset.Subset.antisymm
    · have hh:=(network q hq).polygon_edges_subset_flow v
      rw [recover_flow q hq,hs] at hh
      exact hh
    · exact contour_edges_in_cycle q hq v g w hcont v rfl (Equiv.Perm.SameCycle.refl _ _)
  refine ⟨v,hp,?_⟩
  have hh:=(network q hq).current_on_cycle v q (allLocalIce_conserved q hq)
    (by rw [hp,hs])
  have hi:=(network q hq).oriented_flow_at v ((network q hq).enter v)
  rw [recover_flow q hq] at hi
  simp only [ite_eq_right ((network q hq).distinct v),ite_true,zero_sub] at hi
  simpa [hi] using hh.symm

end IceNetwork

 
noncomputable def polygonCurrent (P : Polygon M) : Edge M →₀ ℤ :=
  wordFlow (polygonGerm P) (polygonWord P)

theorem polygonCurrent_support (P : Polygon M) : (polygonCurrent P).support=P.val := by
  obtain ⟨_,hN,hc,he⟩:=polygon_witness P
  rw [polygonCurrent,simple_word_support _ _ hN hc,he]

theorem polygonCurrent_localIce (P : Polygon M) : ∀ v,LocalIce (polygonCurrent P) v :=
  simple_word_localIce _ _ (polygon_witness P).2.1 (polygon_witness P).2.2.1

 

theorem polygon_current_two_orientations (P : Polygon M) (r : Edge M →₀ ℤ)
    (hr : ∀ v,LocalIce r v) (hs : r.support=P.val) :
    r=polygonCurrent P ∨ r= -polygonCurrent P := by
  let q:=polygonCurrent P
  let hq:=polygonCurrent_localIce P
  let C:=IceNetwork.network q hq
  obtain ⟨v,hv,hc⟩:=IceNetwork.polygon_of_word q hq (polygonGerm P) (polygonWord P)
    (polygon_witness P).1 (polygon_witness P).2.1 (polygon_witness P).2.2.1 rfl
  have he : C.polygon v=P := Subtype.ext (hv.trans (polygon_witness P).2.2.2)
  have hh:=C.two_orientations v r hr (by rw [he]; exact hs)
  change C.componentFlow (C.polygon v)=q at hc
  rw [hc] at hh
  exact hh

end PolynomialVacuumCylinder

end OAI
