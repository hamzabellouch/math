import OAI.Combinatorics.Crossing.InnerDrawingPassages

namespace OAI

noncomputable section
namespace Zarankiewicz.DrawingPassages
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n}

theorem innerIndex_eq_of_edge_mark (C : DrawingPassages D) (p q : C.InnerIndex)
    (he : p.1=q.1) (hm : C.innerMark p=C.innerMark q) : p=q := by
  rcases p with ⟨e,i⟩
  rcases q with ⟨f,j⟩
  change e=f at he
  subst f
  congr 1
  apply Subtype.ext
  exact (C.increasing e).injective (D.edge_injective e (congrArg Subtype.val hm))

theorem incomingPort_injective (C : DrawingPassages D) : Function.Injective C.incomingPort := by
  intro p q he
  apply C.innerIndex_eq_of_edge_mark p q (congrArg (fun x : C.Port => x.1.1) he)
  have hh := congrArg C.portMark he
  simpa only [C.incomingPort_mark] using hh

theorem outgoingPort_injective (C : DrawingPassages D) : Function.Injective C.outgoingPort := by
  intro p q he
  apply C.innerIndex_eq_of_edge_mark p q (congrArg (fun x : C.Port => x.1.1) he)
  have hh := congrArg C.portMark he
  simpa only [C.outgoingPort_mark] using hh

theorem incomingPort_ne_outgoingPort (C : DrawingPassages D) (p q : C.InnerIndex) :
    C.incomingPort p ≠ C.outgoingPort q := by
  intro he
  have hh : true=false := congrArg Prod.snd he
  cases hh

theorem incomingPoint_on_circle (C : DrawingPassages D) (p : C.InnerIndex) :
    squaredLength (C.portPoint (C.incomingPort p)-(C.innerMark p).val)=C.radius^2 := by
  simpa only [C.incomingPort_mark] using C.portPoint_on_circle (C.incomingPort p)

theorem outgoingPoint_on_circle (C : DrawingPassages D) (p : C.InnerIndex) :
    squaredLength (C.portPoint (C.outgoingPort p)-(C.innerMark p).val)=C.radius^2 := by
  simpa only [C.outgoingPort_mark] using C.portPoint_on_circle (C.outgoingPort p)

theorem crossing_chords_transverse_at_mark (C : DrawingPassages D) (p q : C.InnerIndex)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) :
    SegmentPairTransverse (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p))
      (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q)) := by
  apply round_circle_chords_transverse (C.innerMark p).val _ _ _ _ C.radius
  · exact C.incomingPoint_on_circle p
  · exact C.outgoingPoint_on_circle p
  · simpa only [hm] using C.incomingPoint_on_circle q
  · simpa only [hm] using C.outgoingPoint_on_circle q
  · exact C.portPoint_injective.ne (C.incomingPort_ne_outgoingPort p p)
  · exact C.portPoint_injective.ne (C.incomingPort_ne_outgoingPort q q)
  · exact C.portPoint_injective.ne (C.incomingPort_injective.ne hpq)
  · exact C.portPoint_injective.ne (C.incomingPort_ne_outgoingPort p q)
  · exact C.portPoint_injective.ne (Ne.symm (C.incomingPort_ne_outgoingPort q p))
  · exact C.portPoint_injective.ne (C.outgoingPort_injective.ne hpq)

theorem innerMark_no_triples (C : DrawingPassages D) (p q r : C.InnerIndex)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hpqM : C.innerMark p=C.innerMark q) (hprM : C.innerMark p=C.innerMark r) : False := by
  have heq : p.1 ≠ q.1 := fun he => hpq (C.innerIndex_eq_of_edge_mark p q he hpqM)
  have her : p.1 ≠ r.1 := fun he => hpr (C.innerIndex_eq_of_edge_mark p r he hprM)
  have hqrM : C.innerMark q=C.innerMark r := hpqM.symm.trans hprM
  have hfr : q.1 ≠ r.1 := fun he => hqr (C.innerIndex_eq_of_edge_mark q r he hqrM)
  have hp : (C.innerMark p).val ∈ edgeInterior D.toContinuousDrawing p.1 :=
    ⟨C.node p.1 p.2.val,C.inner_parameter_interior p,rfl⟩
  have hq : (C.innerMark p).val ∈ edgeInterior D.toContinuousDrawing q.1 := by
    rw [hpqM]
    exact ⟨C.node q.1 q.2.val,C.inner_parameter_interior q,rfl⟩
  have hr : (C.innerMark p).val ∈ edgeInterior D.toContinuousDrawing r.1 := by
    rw [hprM]
    exact ⟨C.node r.1 r.2.val,C.inner_parameter_interior r,rfl⟩
  have hmem : (C.innerMark p).val ∈ edgeInterior D.toContinuousDrawing p.1 ∩
      edgeInterior D.toContinuousDrawing q.1 ∩ edgeInterior D.toContinuousDrawing r.1 := ⟨⟨hp,hq⟩,hr⟩
  rw [D.no_triples p.1 q.1 r.1 heq her hfr] at hmem
  exact hmem

end Zarankiewicz.DrawingPassages

end

end OAI
