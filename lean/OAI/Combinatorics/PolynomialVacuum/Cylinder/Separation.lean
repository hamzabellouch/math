import OAI.Combinatorics.PolynomialVacuum.Cylinder.Support

namespace OAI

namespace PolynomialVacuumCylinder
variable {M : ℕ}

def RootReach (E : Finset (Edge M)) (L R a : Face M) : Prop :=
  Relation.ReflTransGen (DualAdjacent E) L a ∨ Relation.ReflTransGen (DualAdjacent E) R a

def SideReach (E : Finset (Edge M)) (L R : Face M) (g : Germ M) : Prop :=
  RootReach E L R (leftFace g) ∧ RootReach E L R (rightFace g)

theorem RootReach.trans {E : Finset (Edge M)} {L R a b : Face M}
    (h : RootReach E L R a) (hab : Relation.ReflTransGen (DualAdjacent E) a b) : RootReach E L R b := by
  rcases h with h | h
  · exact Or.inl (h.trans hab)
  · exact Or.inr (h.trans hab)

theorem SideReach.reverse {E : Finset (Edge M)} {L R : Face M} {g : Germ M}
    (h : SideReach E L R g) : SideReach E L R (reverseGerm g) := by
  exact ⟨h.2,by simpa only [rightFace_reverse] using h.1⟩

theorem SideReach.canonical {E : Finset (Edge M)} {L R : Face M} {g : Germ M}
    (h : SideReach E L R g) : SideReach E L R (canonicalDart (edgeOf g)) := by
  rcases canonicalDart_edgeOf g with he | he
  · exact he ▸ h
  · exact he ▸ h.reverse

theorem wordContour_edge_reach (q : Edge M →₀ ℤ) (L R : Face M) (g : Germ M) (w : List Bool)
    (hw : WordContour q g w) (hg : SideReach q.support L R g)
    (e : Edge M) (he : e∈tracedEdges g w) : SideReach q.support L R (canonicalDart e) := by
  induction w generalizing g with
  | nil => simp [tracedEdges] at he
  | cons b w ih =>
    have hstep := localContour_side_reach q g b hw.1
    have hs : SideReach q.support L R (advance g b) := ⟨hg.1.trans hstep.2,hg.2.trans hstep.1⟩
    simp only [tracedEdges,Finset.mem_insert] at he
    rcases he with rfl | he
    · have hc := hs.reverse.canonical
      simpa only [reverseGerm_advance] using hc
    · exact ih (advance g b) hw.2 hs he

theorem dualAdjacent_empty_horizontal (i : ZMod M) (j : ℤ) :
    DualAdjacent ∅ (i,j) (i+1,j) := by
  refine ⟨((i+1,j),0),by simp,Or.inr ?_⟩
  simp [leftFace,rightFace,reverseGerm,neighbor]

theorem dualAdjacent_empty_vertical (i : ZMod M) (j : ℤ) :
    DualAdjacent ∅ (i,j) (i,j+1) := by
  refine ⟨((i+1,j),2),by simp,Or.inl ?_⟩
  simp [leftFace,rightFace,reverseGerm,neighbor]

theorem dualReach_empty_horizontal (i : ZMod M) (j : ℤ) (d : ℤ) :
    Relation.ReflTransGen (DualAdjacent ∅) (i,j) (i+d,j) := by
  induction d using Int.induction_on with
  | zero => simpa using (Relation.ReflTransGen.refl (a:=(i,j)) : Relation.ReflTransGen (DualAdjacent ∅) (i,j) (i,j))
  | succ n ih =>
    have he : i+(((n : ℤ)+1 : ℤ) : ZMod M)=i+n+1 := by push_cast; ring
    rw [he]
    apply ih.tail
    simpa using (dualAdjacent_empty_horizontal (i+(n : ZMod M)) j)
  | pred n ih =>
    have he : i+((-(n : ℤ)-1 : ℤ) : ZMod M)+1=i+((-(n : ℤ) : ℤ) : ZMod M) := by push_cast; ring
    apply ih.tail
    rw [← he]
    exact (dualAdjacent_empty_horizontal (i+((-(n : ℤ)-1 : ℤ) : ZMod M)) j).symm

theorem dualReach_empty_vertical (i : ZMod M) (j d : ℤ) :
    Relation.ReflTransGen (DualAdjacent ∅) (i,j) (i,j+d) := by
  induction d using Int.induction_on with
  | zero => simpa using (Relation.ReflTransGen.refl (a:=(i,j)) : Relation.ReflTransGen (DualAdjacent ∅) (i,j) (i,j))
  | succ n ih =>
    rw [show j+((n : ℤ)+1)=j+n+1 by ring]
    exact ih.tail (dualAdjacent_empty_vertical i (j+n))
  | pred n ih =>
    apply ih.tail
    rw [show j+(-(n : ℤ))=j+(-(n : ℤ)-1)+1 by ring]
    exact (dualAdjacent_empty_vertical i (j+(-(n : ℤ)-1))).symm

theorem dualReach_empty (a b : Face M) : Relation.ReflTransGen (DualAdjacent ∅) a b := by
  obtain ⟨d,hd⟩ := ZMod.intCast_surjective (b.1-a.1)
  have hx := dualReach_empty_horizontal a.1 a.2 d
  rw [hd] at hx
  have hy := dualReach_empty_vertical b.1 a.2 (b.2-a.2)
  have he : a.1+(b.1-a.1)=b.1 := by ring
  rw [he] at hx
  simpa using hx.trans hy

theorem all_faces_rootReach (E : Finset (Edge M)) (L R : Face M)
    (hs : ∀ e∈E, SideReach E L R (canonicalDart e)) (a : Face M) : RootReach E L R a := by
  have hp := dualReach_empty L a
  induction hp with
  | refl => exact Or.inl .refl
  | @tail a b hp hab ih =>
    obtain ⟨e,_,h⟩ := hab
    by_cases he : e∈E
    · rcases h with ⟨hl,hr⟩ | ⟨hl,hr⟩
      · exact hr ▸ (hs e he).2
      · exact hl ▸ (hs e he).1
    · exact ih.trans (.single ⟨e,he,h⟩)

theorem representsFlow_constant_on_reach (p : Face M → ℤ) (q : Edge M →₀ ℤ)
    (hp : RepresentsFlow p q) {a b : Face M}
    (h : Relation.ReflTransGen (DualAdjacent q.support) a b) : p a=p b := by
  induction h with
  | refl => rfl
  | @tail b c h hbc ih =>
    obtain ⟨e,he,hlr⟩ := hbc
    have hz : q e=0 := by simpa only [Finsupp.mem_support_iff,not_not] using he
    have hgrad := hp (canonicalDart e)
    have hflow : orientedFlow q (canonicalDart e)=q e := by
      exact orientedFlow_up q e.1.1 e.1.2 e.2
    rw [hflow,hz] at hgrad
    change 0=p (leftFace (.up e.1.1 e.1.2,e.2))-p (rightFace (.up e.1.1 e.1.2,e.2)) at hgrad
    rcases hlr with ⟨hl,hr⟩ | ⟨hl,hr⟩
    all_goals rw [hl,hr] at hgrad; exact ih.trans (by omega)

 

theorem cylinder_separation_iff (g : Germ M) (w : List Bool) (hne : w≠[])
    (hN : (traced g w).Nodup) (hc : terminalGerm g w=g) (a b : Face M) :
    Relation.ReflTransGen (DualAdjacent (tracedEdges g w)) a b ↔
      potential (wordFlow g w) a=potential (wordFlow g w) b := by
  let q := wordFlow g w
  let p := potential q
  have hsupport := simple_word_support g w hN hc
  change q.support=tracedEdges g w at hsupport
  rw [← hsupport]
  have hp : RepresentsFlow p q := closed_word_has_potential g w hc
  constructor
  · exact representsFlow_constant_on_reach p q hp
  · intro hab
    have hs : ∀ e∈q.support, SideReach q.support (leftFace g) (rightFace g) (canonicalDart e) := by
      intro e he
      exact wordContour_edge_reach q (leftFace g) (rightFace g) g w
        (simple_closed_word_contour g w hN hc) ⟨Or.inl .refl,Or.inr .refl⟩ e (hsupport ▸ he)
    have ha := all_faces_rootReach q.support (leftFace g) (rightFace g) hs a
    have hb := all_faces_rootReach q.support (leftFace g) (rightFace g) hs b
    have hdiff : p (leftFace g)≠p (rightFace g) := by
      have hlocal := simple_closed_word_contour g w hN hc
      cases w with
      | nil => exact False.elim (hne rfl)
      | cons b w =>
        have hi := hlocal.1 g.2
        have hslot : g.2≠outgoingSlot g b := by
          rcases g with ⟨v,k⟩; fin_cases k <;> cases b <;> simp only [outgoingSlot] <;> decide
        rw [hp] at hi
        simp only [ite_eq_right hslot,ite_true] at hi
        change p (leftFace g)-p (rightFace g)=0-1 at hi
        omega
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact (dualReach_symm ha).trans hb
    · exact False.elim (hdiff ((representsFlow_constant_on_reach p q hp ha).trans
        (hab.trans (representsFlow_constant_on_reach p q hp hb).symm)))
    · exact False.elim (hdiff ((representsFlow_constant_on_reach p q hp hb).trans
        (hab.symm.trans (representsFlow_constant_on_reach p q hp ha).symm)))
    · exact (dualReach_symm ha).trans hb

end PolynomialVacuumCylinder

end OAI
