import OAI.Combinatorics.Crossing.SurgeryCrossingContainment

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalExterior
variable {m n : ℕ} {D : AdmissibleDrawing m n} {C : DrawingPassages D.toFiniteIntersectionDrawing}
  (E : PolygonalExterior C) (v : BipartiteVertex m n → Plane) (hvinj : Function.Injective v)
  (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
  (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
    det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
  (P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e))
  {p q : C.InnerIndex}

theorem adjacentSurgeryDrawing_no_triples
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) (hadj : p.1.1=q.1.1 ∨ p.1.2=q.1.2)
    (hcross : SegmentsCrossProperly (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p))
      (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q)))
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (e f g : BipartiteEdge m n) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) :
    edgeInterior (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb) e ∩
      edgeInterior (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb) f ∩
      edgeInterior (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb) g = ∅ := by
  let B := E.assembledAdmissible v hvinj hv hdet
  let A := adjacentSurgeryDrawing Kp Kq hm hadj hv hemb
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨⟨hxe,hxf⟩,hxg⟩ := hx
  have havoid : ∀ j, x ≠ B.vertex j := edgeInterior_not_vertex A e x hxe
  have hthree (a b c : BipartiteEdge m n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
      (ha : x ∈ Set.range (B.edge a)) (hb : x ∈ Set.range (B.edge b))
      (hc : x ∈ Set.range (B.edge c)) : False := by
    have hmem : x ∈ edgeInterior B.toContinuousDrawing a ∩ edgeInterior B.toContinuousDrawing b ∩
        edgeInterior B.toContinuousDrawing c :=
      ⟨⟨edgeInterior_of_range_not_vertices _ a x ha havoid,
        edgeInterior_of_range_not_vertices _ b x hb havoid⟩,edgeInterior_of_range_not_vertices _ c x hc havoid⟩
    rw [B.no_triples a b c hab hac hbc] at hmem
    exact hmem
  have htwo (a : BipartiteEdge m n) (hap : a ≠ p.1) (haq : a ≠ q.1)
      (hp : x ∈ Set.range (adjacentSurgeryRouteP Kp Kq hm hadj))
      (hq : x ∈ Set.range (adjacentSurgeryRouteQ Kp Kq hm hadj))
      (ha : x ∈ Set.range (B.edge a)) : False := by
    have hh := E.adjacentSurgeryRoutes_meeting_each_other v hvinj hv hdet P Kp Kq hpq hm hadj hcross x hp hq
    exact hthree p.1 q.1 a (fun he => hpq (C.innerIndex_eq_of_edge_mark p q he hm))
      (Ne.symm hap) (Ne.symm haq) hh.1 hh.2 ha
  have hone (a b : BipartiteEdge m n) (hab : a ≠ b)
      (hap : a ≠ p.1) (haq : a ≠ q.1) (hbp : b ≠ p.1) (hbq : b ≠ q.1)
      (hh : x ∈ Set.range (adjacentSurgeryRouteP Kp Kq hm hadj) ∨
        x ∈ Set.range (adjacentSurgeryRouteQ Kp Kq hm hadj))
      (ha : x ∈ Set.range (B.edge a)) (hb : x ∈ Set.range (B.edge b)) : False := by
    rcases E.adjacentSurgeryRoutes_meeting_other v hvinj hv hdet P Kp Kq hpq hm hadj a hap haq x hh ha with hp | hq
    · exact hthree p.1 a b (Ne.symm hap) (Ne.symm hbp) hab hp ha hb
    · exact hthree q.1 a b (Ne.symm haq) (Ne.symm hbq) hab hq ha hb
  have hcases (a : BipartiteEdge m n) (ha : x ∈ Set.range (A.edge a)) :=
    B.toContinuousDrawing.replaceTwoRoutes_range_cases p.1 q.1 (adjacentSurgeryRouteP Kp Kq hm hadj)
      (adjacentSurgeryRouteQ Kp Kq hm hadj) a x ha
  have hec := hcases e (edgeInterior_subset_range A e hxe)
  have hfc := hcases f (edgeInterior_subset_range A f hxf)
  have hgc := hcases g (edgeInterior_subset_range A g hxg)
  rcases hec with ⟨hep,hx⟩ | ⟨heq,hx⟩ | ⟨hep,heq,hx⟩
  · rcases hfc with ⟨hfp,hy⟩ | ⟨hfq,hy⟩ | ⟨hfp,hfq,hy⟩
    · exact hef (hep.trans hfp.symm)
    · rcases hgc with ⟨hgp,hz⟩ | ⟨hgq,hz⟩ | ⟨hgp,hgq,hz⟩
      · exact heg (hep.trans hgp.symm)
      · exact hfg (hfq.trans hgq.symm)
      · exact htwo g hgp hgq hx hy hz
    · rcases hgc with ⟨hgp,hz⟩ | ⟨hgq,hz⟩ | ⟨hgp,hgq,hz⟩
      · exact heg (hep.trans hgp.symm)
      · exact htwo f hfp hfq hx hz hy
      · exact hone f g hfg hfp hfq hgp hgq (Or.inl hx) hy hz
  · rcases hfc with ⟨hfp,hy⟩ | ⟨hfq,hy⟩ | ⟨hfp,hfq,hy⟩
    · rcases hgc with ⟨hgp,hz⟩ | ⟨hgq,hz⟩ | ⟨hgp,hgq,hz⟩
      · exact hfg (hfp.trans hgp.symm)
      · exact heg (heq.trans hgq.symm)
      · exact htwo g hgp hgq hy hx hz
    · exact hef (heq.trans hfq.symm)
    · rcases hgc with ⟨hgp,hz⟩ | ⟨hgq,hz⟩ | ⟨hgp,hgq,hz⟩
      · exact htwo f hfp hfq hz hx hy
      · exact heg (heq.trans hgq.symm)
      · exact hone f g hfg hfp hfq hgp hgq (Or.inr hx) hy hz
  · rcases hfc with ⟨hfp,hy⟩ | ⟨hfq,hy⟩ | ⟨hfp,hfq,hy⟩
    · rcases hgc with ⟨hgp,hz⟩ | ⟨hgq,hz⟩ | ⟨hgp,hgq,hz⟩
      · exact hfg (hfp.trans hgp.symm)
      · exact htwo e hep heq hy hz hx
      · exact hone e g heg hep heq hgp hgq (Or.inl hy) hx hz
    · rcases hgc with ⟨hgp,hz⟩ | ⟨hgq,hz⟩ | ⟨hgp,hgq,hz⟩
      · exact htwo e hep heq hz hy hx
      · exact hfg (hfq.trans hgq.symm)
      · exact hone e g heg hep heq hgp hgq (Or.inr hy) hx hz
    · rcases hgc with ⟨hgp,hz⟩ | ⟨hgq,hz⟩ | ⟨hgp,hgq,hz⟩
      · exact hone e f hef hep heq hfp hfq (Or.inl hz) hx hy
      · exact hone e f hef hep heq hfp hfq (Or.inr hz) hx hy
      · exact hthree e f g hef heg hfg hx hy hz

end Zarankiewicz.PolygonalExterior

end

end OAI
