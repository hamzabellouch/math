import OAI.Combinatorics.PolynomialVacuum.Cylinder.SystemCurrent

namespace OAI

namespace PolynomialVacuumCylinder
open Classical
variable {M : ℕ}

theorem polygon_edges_nonempty (P : Polygon M) : P.val.Nonempty := by
  obtain ⟨h,_,_,he⟩:=polygon_witness P
  obtain ⟨b,w,hw⟩:=List.exists_cons_of_ne_nil h
  rw [hw,tracedEdges] at he
  rw [← he]
  exact Finset.insert_nonempty _ _

theorem polygonCurrent_ne_zero (P : Polygon M) : polygonCurrent P≠0 := by
  intro h
  have hs:=polygonCurrent_support P
  rw [h,Finsupp.support_zero] at hs
  exact (polygon_edges_nonempty P).ne_empty hs.symm

 
theorem conserved_subpolygon_support (P : Polygon M) (r : Edge M →₀ ℤ)
    (hr : Conserved r) (hs : r.support⊆P.val) (hn : r≠0) : r.support=P.val := by
  let q:=polygonCurrent P
  let hq:=polygonCurrent_localIce P
  let C:=IceNetwork.network q hq
  obtain ⟨v,hv,_⟩:=IceNetwork.polygon_of_word q hq (polygonGerm P) (polygonWord P)
    (polygon_witness P).1 (polygon_witness P).2.1 (polygon_witness P).2.2.1 rfl
  have he : C.polygon v=P := Subtype.ext (hv.trans (polygon_witness P).2.2.2)
  have hc:=C.current_on_cycle v r hr (by rw [he]; exact hs)
  have hz : -orientedFlow r (v.val,C.enter v)≠0 := by
    intro hz
    rw [hz,zero_smul] at hc
    exact hn hc
  rw [hc,Finsupp.support_smul_eq hz,C.componentFlow_support _
    (Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩),he]

theorem polygon_eq_of_subset (P Q : Polygon M) (h : P.val⊆Q.val) : P=Q := by
  apply Subtype.ext
  have hs:=conserved_subpolygon_support Q (polygonCurrent P)
    (allLocalIce_conserved _ (polygonCurrent_localIce P))
    (by rw [polygonCurrent_support]; exact h) (polygonCurrent_ne_zero P)
  simpa only [polygonCurrent_support] using hs

theorem edge_vertices_subset_polygon (P : Polygon M) (e : Edge M) (he : e∈P.val) :
    edgeVertices e⊆P.vertices := by
  intro v hv
  exact Finset.mem_biUnion.mpr ⟨e,he,hv⟩

theorem system_edges_disjoint (S : Finset (Polygon M))
    (hS : (S : Set (Polygon M)).Pairwise (fun P Q => Disjoint P.vertices Q.vertices)) :
    (S : Set (Polygon M)).Pairwise (fun P Q => Disjoint P.val Q.val) := by
  intro P hP Q hQ hne
  apply Finset.disjoint_left.mpr
  intro e heP heQ
  have hu : upEnd e∈edgeVertices e := by simp [edgeVertices,upEnd]
  exact Finset.disjoint_left.mp (hS hP hQ hne)
    (edge_vertices_subset_polygon P e heP hu) (edge_vertices_subset_polygon Q e heQ hu)

 
theorem systemCurrent_support (S : Finset (Polygon M)) (o : Polygon M → Bool)
    (hS : (S : Set (Polygon M)).Pairwise (fun P Q => Disjoint P.vertices Q.vertices)) :
    (systemCurrent S o).support=S.biUnion Subtype.val := by
  ext e
  constructor
  · intro he
    by_contra hn
    apply Finsupp.mem_support_iff.mp he
    simp only [systemCurrent,Finsupp.coe_finsetSum,Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro P hP
    apply Finsupp.notMem_support_iff.mp
    rw [signedPolygonCurrent_support]
    exact fun heP => hn (Finset.mem_biUnion.mpr ⟨P,hP,heP⟩)
  · intro he
    obtain ⟨P,hP,heP⟩:=Finset.mem_biUnion.mp he
    have hv : upEnd e∈P.vertices :=
      edge_vertices_subset_polygon P e heP (by simp [edgeVertices,upEnd])
    have hh:=systemCurrent_at S o hS P hP (upEnd e) hv e.2
    have hn : (signedPolygonCurrent P (o P)) e≠0 := by
      apply Finsupp.mem_support_iff.mp
      rw [signedPolygonCurrent_support]
      exact heP
    apply Finsupp.mem_support_iff.mpr
    have heq : systemCurrent S o e=signedPolygonCurrent P (o P) e := by
      simpa only [upEnd,orientedFlow_up] using hh
    exact heq.trans_ne hn

end PolynomialVacuumCylinder

end OAI
