import OAI.Combinatorics.PolynomialVacuum.Cylinder.Indicator

namespace OAI

namespace PolynomialVacuumCylinder
variable {M : ℕ}

theorem orientedFlow_eq (q : Edge M →₀ ℤ) (g : Germ M) :
    orientedFlow q g=dartSign g * q (edgeOf g) := by
  rcases g with ⟨v,k⟩
  cases v <;> simp [orientedFlow_up,orientedFlow_down,dartSign,edgeOf]

theorem wordFlow_support_subset (g : Germ M) (w : List Bool) :
    (wordFlow g w).support ⊆ tracedEdges g w := by
  intro e he
  induction w generalizing g with
  | nil => simp [wordFlow] at he
  | cons b w ih =>
    simp only [tracedEdges,Finset.mem_insert]
    by_cases h : e=edgeOf (g.1,outgoingSlot g b)
    · exact Or.inl h
    · right
      apply ih
      simpa [wordFlow,dartFlow,Finsupp.single_apply,Ne.symm h] using he

theorem wordContour_edge_nonzero (q : Edge M →₀ ℤ) (g : Germ M) (w : List Bool)
    (hw : WordContour q g w) (e : Edge M) (he : e∈tracedEdges g w) : q e≠0 := by
  induction w generalizing g with
  | nil => simp [tracedEdges] at he
  | cons b w ih =>
    simp only [tracedEdges,Finset.mem_insert] at he
    rcases he with rfl | he
    · have h := hw.1 (outgoingSlot g b)
      have hn : outgoingSlot g b≠g.2 := by
        rcases g with ⟨v,k⟩; fin_cases k <;> cases b <;> simp only [outgoingSlot] <;> decide
      rw [orientedFlow_eq] at h
      simp only [ite_true,ite_eq_right hn,sub_zero] at h
      intro hz
      rw [hz,mul_zero] at h
      omega
    · exact ih (advance g b) hw.2 he

theorem simple_word_support (g : Germ M) (w : List Bool)
    (hN : (traced g w).Nodup) (hc : terminalGerm g w=g) :
    (wordFlow g w).support=tracedEdges g w := by
  apply Finset.Subset.antisymm (wordFlow_support_subset g w)
  intro e he
  exact Finsupp.mem_support_iff.mpr (wordContour_edge_nonzero _ g w (simple_closed_word_contour g w hN hc) e he)

theorem DualAdjacent.symm {E : Finset (Edge M)} {a b : Face M} (h : DualAdjacent E a b) :
    DualAdjacent E b a := by
  obtain ⟨e,he,hab⟩ := h
  exact ⟨e,he,hab.symm⟩

theorem dualReach_symm {E : Finset (Edge M)} {a b : Face M}
    (h : Relation.ReflTransGen (DualAdjacent E) a b) :
    Relation.ReflTransGen (DualAdjacent E) b a := by
  induction h with
  | refl => rfl
  | tail h hab ih => exact (Relation.ReflTransGen.single hab.symm).trans ih

theorem dualAdjacent_of_zero (q : Edge M →₀ ℤ) (g : Germ M)
    (hz : orientedFlow q g=0) : DualAdjacent q.support (leftFace g) (rightFace g) := by
  have he : edgeOf g∉q.support := by
    simp only [Finsupp.mem_support_iff,not_not]
    rw [orientedFlow_eq] at hz
    have hs : dartSign g≠0 := by rcases g with ⟨v,k⟩; cases v <;> simp [dartSign]
    exact (mul_eq_zero.mp hz).resolve_left hs
  refine ⟨edgeOf g,he,?_⟩
  rcases canonicalDart_edgeOf g with h | h
  · left; exact ⟨congrArg leftFace h,congrArg rightFace h⟩
  · right
    refine ⟨congrArg leftFace h,?_⟩
    change rightFace (canonicalDart (edgeOf g))=leftFace g
    simpa using congrArg rightFace h

 

theorem localContour_side_reach (q : Edge M →₀ ℤ) (g : Germ M) (b : Bool)
    (h : LocalContour q g b) :
    Relation.ReflTransGen (DualAdjacent q.support) (rightFace g) (rightFace (advance g b)) ∧
    Relation.ReflTransGen (DualAdjacent q.support) (leftFace g) (leftFace (advance g b)) := by
  let k : Fin 3 := g.2+(if b then 1 else 2)
  have hk : orientedFlow q (g.1,k)=0 := by
    rw [h]
    rcases g with ⟨v,l⟩
    fin_cases l <;> cases b <;> norm_num [k,outgoingSlot]
  have ha := Relation.ReflTransGen.single (dualAdjacent_of_zero q (g.1,k) hk)
  have hb := dualReach_symm ha
  rcases g with ⟨v,l⟩
  cases v <;> fin_cases l <;> cases b <;>
    simp [advance,outgoingSlot,k,leftFace,rightFace,reverseGerm,neighbor] at ha hb ⊢ <;>
    exact ⟨by first | rfl | exact ha,by first | rfl | exact ha | exact hb⟩

theorem wordContour_side_reach (q : Edge M →₀ ℤ) (g : Germ M) (w : List Bool)
    (h : WordContour q g w) :
    Relation.ReflTransGen (DualAdjacent q.support) (rightFace g) (rightFace (terminalGerm g w)) ∧
    Relation.ReflTransGen (DualAdjacent q.support) (leftFace g) (leftFace (terminalGerm g w)) := by
  induction w generalizing g with
  | nil => exact ⟨.refl,.refl⟩
  | cons b w ih =>
    have hloc := localContour_side_reach q g b h.1
    have htail := ih (advance g b) h.2
    exact ⟨hloc.1.trans htail.1,hloc.2.trans htail.2⟩

end PolynomialVacuumCylinder

end OAI
