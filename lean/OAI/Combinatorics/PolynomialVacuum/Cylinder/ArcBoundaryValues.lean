import OAI.Combinatorics.PolynomialVacuum.Cylinder.HalfArcs

namespace OAI

namespace PolynomialVacuumCylinder
open Classical
variable {M H : ℕ} [NeZero M]

theorem halfArch_terminal (A : PolynomialVacuumBridge.Corridor.ArchWord.CylinderArch M) (hH : A.val.height≤H) :
    terminalGerm (halfArchToBand A hH).start (halfArchToBand A hH).word=(.down A.val.endX (-1),0) := by
  have hp : projectGerm M PolynomialVacuumBridge.Corridor.bottomSource=(.up (0 : ZMod M) 0,0) := by
    simp [projectGerm,projectVertex,PolynomialVacuumBridge.Corridor.bottomSource]
  change terminalGerm (.up (0 : ZMod M) 0,0) A.val.word=_
  rw [← hp,← project_terminal,A.val.terminal]
  rfl

theorem atPort_terminal (A : PolynomialVacuumBridge.Corridor.ArchWord.CylinderArch M) (hH : A.val.height≤H)
    (p : Bool × ZMod M) : terminalGerm (atPort A hH p).start (atPort A hH p).word=
      if p.1 then (.up (-A.val.endX+p.2) H,0) else (.down (A.val.endX+p.2) (-1),0) := by
  unfold atPort
  split_ifs with hp
  · change terminalGerm (mapGerm (translate p.2 0) (mapGerm (rotate H) (halfArchToBand A hH).start))
        (halfArchToBand A hH).word=_
    rw [← map_terminal _ (translate_neighbor_cyl _ _),← map_terminal _ (rotate_neighbor _),halfArch_terminal]
    simp [mapGerm,translate,rotate]
  · change terminalGerm (mapGerm (translate p.2 0) (halfArchToBand A hH).start) (halfArchToBand A hH).word=_
    rw [← map_terminal _ (translate_neighbor_cyl _ _),halfArch_terminal]
    simp [mapGerm,translate]

theorem BoundaryArc.outside_current (A : BoundaryArc (bandSites M H)) (g : Germ M)
    (hg : g.1∉bandSites M H) :
    orientedFlow A.current g=(if reverseGerm A.start=g then 1 else 0)-(if terminalGerm A.start A.word=g then 1 else 0) := by
  have ht : turnVisit A.start A.word g=0 := turnVisit_eq_zero_of_not_mem _ _ _ _ (fun hv => hg (A.inside _ hv))
  simp only [BoundaryArc.current,orientedFlow_arc,Finsupp.sub_apply,Finsupp.add_apply,Finsupp.single_apply,ht,zero_add]

noncomputable def halfArcBottom (A : PolynomialVacuumBridge.Corridor.ArchWord.CylinderArch M) (p : Bool × ZMod M) (i : ZMod M) : ℤ :=
  if p.1 then 0 else (if A.val.endX+p.2=i then 1 else 0)-(if p.2=i then 1 else 0)
noncomputable def halfArcTop (A : PolynomialVacuumBridge.Corridor.ArchWord.CylinderArch M) (p : Bool × ZMod M) (i : ZMod M) : ℤ :=
  if p.1 then (if p.2=i then 1 else 0)-(if -A.val.endX+p.2=i then 1 else 0) else 0

theorem atPort_bottom_current (A : PolynomialVacuumBridge.Corridor.ArchWord.CylinderArch M) (hH : A.val.height≤H)
    (p : Bool × ZMod M) (i : ZMod M) : (atPort A hH p).current ((i,0),0)=halfArcBottom A p i := by
  have hh:=(atPort A hH p).outside_current (.down i (-1),0) (by simp [mem_bandSites,InBand,vertexLayer])
  simp only [orientedFlow_down,edgeOf] at hh
  norm_num only at hh
  rw [atPort_terminal,atPort_start] at hh
  rcases p with ⟨b,j⟩
  cases b <;> simp [halfArcBottom,reverseGerm,neighbor] at hh ⊢ <;> omega

theorem atPort_top_current (A : PolynomialVacuumBridge.Corridor.ArchWord.CylinderArch M) (hH : A.val.height≤H)
    (p : Bool × ZMod M) (i : ZMod M) : (atPort A hH p).current ((i,(H : ℤ)),0)=halfArcTop A p i := by
  have hh:=(atPort A hH p).outside_current (.up i H,0) (by simp [mem_bandSites,InBand,vertexLayer])
  simp only [orientedFlow_up] at hh
  rw [atPort_terminal,atPort_start] at hh
  rcases p with ⟨b,j⟩
  cases b <;> simpa [halfArcTop,reverseGerm,neighbor] using hh
end PolynomialVacuumCylinder

end OAI
