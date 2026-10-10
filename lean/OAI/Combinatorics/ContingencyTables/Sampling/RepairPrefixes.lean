import OAI.Combinatorics.ContingencyTables.Sampling.Repair

namespace OAI

/-! # Literal repair values and row-major prefix preservation -/

namespace ContingencyTables

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [Fintype I] [Fintype J] in
lemma IsDefect.negative_entry {x q : I → J → ℕ} {s t : I×J}
    (h : IsDefect x q s t) : q s.1 s.2=x s.1 s.2+1 := by
  have hst : ¬(s.1=t.1 ∧ s.2=t.2) := by
    rintro ⟨h1,h2⟩
    exact h.1 (Prod.ext h1 h2)
  have he := h.2 s.1 s.2
  simp only [transferInt,hst,↓reduceIte,and_self,sub_zero] at he
  omega

omit [Fintype I] [Fintype J] in
lemma repairMatrix_unchanged {x q : I → J → ℕ} {s t w : I×J}
    (h : IsDefect x q s t) (hwt : w ≠ t) (hwv : w ≠ (t.1,s.2)) :
    repairMatrix x s t w.1 w.2=x w.1 w.2 := by
  apply Int.natCast_inj.mp
  rw [repairMatrix_cast h]
  have h1 : ¬(w.1=t.1 ∧ w.2=t.2) := fun hw => hwt (Prod.ext hw.1 hw.2)
  have h2 : ¬(w.1=t.1 ∧ w.2=s.2) := fun hw => hwv (Prod.ext hw.1 hw.2)
  simp only [transferInt,h1,h2,↓reduceIte,sub_zero,add_zero]

omit [Fintype I] [Fintype J] in
lemma repairMatrix_special {x q : I → J → ℕ} {s t : I×J}
    (h : IsDefect x q s t) :
    repairMatrix x s t s.1 s.2=x s.1 s.2+(if t.1=s.1 then 1 else 0) := by
  apply Int.natCast_inj.mp
  rw [repairMatrix_cast h]
  have hst : ¬(s.1=t.1 ∧ s.2=t.2) := fun hw => h.1 (Prod.ext hw.1 hw.2)
  simp only [transferInt,hst,↓reduceIte,sub_zero,Nat.cast_add]
  by_cases hr : t.1=s.1
  · simp [hr]
  · simp [hr,Ne.symm hr]

def RowMajorBefore [LT I] [LT J] (s t : I×J) : Prop :=
  s.1<t.1 ∨ s.1=t.1 ∧ s.2<t.2

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
lemma RowMajorBefore.trans [LinearOrder I] [LinearOrder J] {r s t : I×J}
    (hrs : RowMajorBefore r s) (hst : RowMajorBefore s t) : RowMajorBefore r t := by
  rcases hrs with hrs|⟨hrs,hc⟩
  · rcases hst with hst|⟨hst,_⟩
    · exact Or.inl (lt_trans hrs hst)
    · exact Or.inl (hst ▸ hrs)
  · rcases hst with hst|⟨hst,htc⟩
    · exact Or.inl (hrs ▸ hst)
    · exact Or.inr ⟨hrs.trans hst,lt_trans hc htc⟩

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
lemma RowMajorBefore.ne [LinearOrder I] [LinearOrder J] {s t : I×J}
    (h : RowMajorBefore s t) : s ≠ t := by
  intro he
  subst t
  rcases h with h|⟨_,h⟩ <;> exact lt_irrefl _ h

omit [Fintype I] [Fintype J] in
theorem repairMatrix_prefix [LinearOrder I] [LinearOrder J]
    {x q : I → J → ℕ} {s t w : I×J} (h : IsDefect x q s t)
    (hst : RowMajorBefore s t) (hws : RowMajorBefore w s) :
    repairMatrix x s t w.1 w.2=x w.1 w.2 := by
  apply repairMatrix_unchanged h (hws.trans hst).ne
  intro hw
  have hv : RowMajorBefore w (t.1,s.2) := by
    rcases hst with hr|⟨hr,_⟩
    · exact hws.trans (Or.inl hr)
    · simpa only [←hr] using hws
  exact hv.ne hw

end ContingencyTables

end OAI
