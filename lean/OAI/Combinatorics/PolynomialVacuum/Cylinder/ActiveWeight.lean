import OAI.Combinatorics.PolynomialVacuum.Cylinder.LocalTurn

namespace OAI

namespace PolynomialVacuumCylinder
open Classical
variable {M : ℕ}

theorem activeSites_eq_support_vertices (r : Edge M →₀ ℤ) :
    activeSites r=r.support.biUnion edgeVertices := by
  ext v
  rw [mem_activeSites,Finset.mem_biUnion]
  constructor
  · rintro ⟨k,hk⟩
    refine ⟨edgeOf (v,k),Finsupp.mem_support_iff.mpr ?_,by simp⟩
    exact fun h => hk ((orientedFlow_eq_zero_iff r (v,k)).mpr h)
  · rintro ⟨⟨⟨i,j⟩,k⟩,he,hv⟩
    have hn:=Finsupp.mem_support_iff.mp he
    simp only [edgeVertices,Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact ⟨k,by simpa only [orientedFlow_up] using hn⟩
    · refine ⟨k,?_⟩
      have hh:=orientedFlow_reverse r (Vertex.up i j,k)
      simp only [reverseGerm,orientedFlow_up] at hh
      rw [hh]
      exact neg_ne_zero.mpr hn

@[simp] theorem signedPolygonCurrent_active (P : Polygon M) (o : Bool) :
    activeSites (signedPolygonCurrent P o)=P.vertices := by
  rw [activeSites_eq_support_vertices,signedPolygonCurrent_support]
  rfl

theorem systemCurrent_active (S : Finset (Polygon M)) (o : Polygon M → Bool)
    (hS : (S : Set (Polygon M)).Pairwise (fun P Q => Disjoint P.vertices Q.vertices)) :
    activeSites (systemCurrent S o)=S.biUnion Polygon.vertices := by
  let C:=IceNetwork.network (systemCurrent S o) (systemCurrent_localIce S o hS)
  have hp:=C.polygons_vertices
  change _=activeSites (systemCurrent S o) at hp
  rw [systemCurrent_polygons S o hS] at hp
  exact hp.symm

noncomputable def flowTurn (r : Edge M →₀ ℤ) : ℤ :=
  ∑ v∈activeSites r,localTurn r v

@[simp] theorem flowTurn_polygon (P : Polygon M) :
    flowTurn (polygonCurrent P)=PolynomialVacuumBridge.Corridor.turnUnits (polygonWord P) := by
  unfold flowTurn
  have hs:=signedPolygonCurrent_active P true
  simp only [signedPolygonCurrent,ite_true] at hs
  rw [hs,polygon_turn_sum]

@[simp] theorem activeSites_neg (r : Edge M →₀ ℤ) : activeSites (-r)=activeSites r := by
  simp [activeSites,map_neg,Finsupp.support_neg]

@[simp] theorem flowTurn_neg (r : Edge M →₀ ℤ) : flowTurn (-r)= -flowTurn r := by
  simp [flowTurn,Finset.sum_neg_distrib]

theorem systemCurrent_turn (S : Finset (Polygon M)) (o : Polygon M → Bool)
    (hS : (S : Set (Polygon M)).Pairwise (fun P Q => Disjoint P.vertices Q.vertices)) :
    flowTurn (systemCurrent S o)=∑ P∈S,flowTurn (signedPolygonCurrent P (o P)) := by
  unfold flowTurn
  rw [systemCurrent_active S o hS,Finset.sum_biUnion hS]
  apply Finset.sum_congr rfl
  intro P hP
  rw [signedPolygonCurrent_active]
  apply Finset.sum_congr rfl
  intro v hv
  unfold localTurn
  rw [systemCurrent_at S o hS P hP v hv 0,systemCurrent_at S o hS P hP v hv 1,
    systemCurrent_at S o hS P hP v hv 2]

theorem systemCurrent_length (S : Finset (Polygon M)) (o : Polygon M → Bool)
    (hS : (S : Set (Polygon M)).Pairwise (fun P Q => Disjoint P.vertices Q.vertices)) :
    (activeSites (systemCurrent S o)).card=∑ P∈S,P.vertices.card := by
  rw [systemCurrent_active S o hS,Finset.card_biUnion hS]

end PolynomialVacuumCylinder

end OAI
