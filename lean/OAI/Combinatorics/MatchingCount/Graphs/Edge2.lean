import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.Admissible

namespace OAI

namespace MatchingFPRAS.UnitRefresh

open Finset MatchingFPRAS.Transport

variable {V L : Type*} [Fintype V] [Fintype L] [DecidableEq V] [DecidableEq L]

variable {bags : V → Finset L}

noncomputable local instance : Fintype (BagEdge bags) := Fintype.ofFinite _

noncomputable local instance : Fintype (PM (BagEdge.Incident (bags := bags))) := Fintype.ofFinite _

def ColoredPairing.edgeAt (p : ColoredPairing bags) (x : V) : BagEdge bags :=
  ⟨⟨(s(x,p.pair.mate x),p.color x),by
    simp only [Sym2.mk_isDiag_iff]
    exact (p.pair.no_fixed x).symm⟩,by
    intro y hy
    change p.color x ∈ bags y
    rcases Sym2.mem_iff.mp hy with h | h <;> subst y
    · exact p.allowed x
    · rw [←p.same_color x]
      exact p.allowed (p.pair.mate x)⟩

omit [Fintype V] [Fintype L] [DecidableEq V] [DecidableEq L] in
lemma ColoredPairing.edgeAt_incident (p : ColoredPairing bags) (x y : V) :
    (p.edgeAt x).Incident y ↔ y=x ∨ y=p.pair.mate x := Sym2.mem_iff

omit [Fintype V] [Fintype L] [DecidableEq V] [DecidableEq L] in
lemma ColoredPairing.edgeAt_mate (p : ColoredPairing bags) (x : V) :
    p.edgeAt (p.pair.mate x)=p.edgeAt x := by
  apply Subtype.ext
  apply Subtype.ext
  change (s(p.pair.mate x,p.pair.mate (p.pair.mate x)),p.color (p.pair.mate x)) = _
  rw [p.pair.involutive,p.same_color,Sym2.eq_swap]
  rfl

omit [Fintype V] [Fintype L] [DecidableEq V] [DecidableEq L] in
lemma ColoredPairing.edgeAt_of_incident (p : ColoredPairing bags) (x y : V)
    (h : (p.edgeAt x).Incident y) : p.edgeAt y=p.edgeAt x := by
  rcases (p.edgeAt_incident x y).mp h with rfl | rfl
  · rfl
  · exact p.edgeAt_mate x

noncomputable def ColoredPairing.toPM (p : ColoredPairing bags) : PM (BagEdge.Incident (bags := bags)) :=
  ⟨Finset.univ.image p.edgeAt,by
    constructor
    · intros; exact Finset.mem_univ _
    · intro x hx
      refine ⟨p.edgeAt x,⟨Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩,?_⟩,?_⟩
      · exact (p.edgeAt_incident x x).mpr (Or.inl rfl)
      · intro e he
        obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp he.1
        exact (p.edgeAt_of_incident y x he.2).symm⟩

noncomputable def chosenEdge (M : PM (BagEdge.Incident (bags := bags))) (x : V) : BagEdge bags :=
  Classical.choose (M.property.2 x (Finset.mem_univ x))

omit [Fintype L] [DecidableEq V] [DecidableEq L] in
lemma chosenEdge_spec [Fintype L] [DecidableEq V] [DecidableEq L]
    (M : PM (BagEdge.Incident (bags := bags))) (x : V) :
    chosenEdge M x ∈ M.val ∧ (chosenEdge M x).Incident x :=
  (Classical.choose_spec (M.property.2 x (Finset.mem_univ x))).1

omit [Fintype L] [DecidableEq V] [DecidableEq L] in
lemma chosenEdge_unique [Fintype L] [DecidableEq V] [DecidableEq L]
    (M : PM (BagEdge.Incident (bags := bags))) (x : V) (e : BagEdge bags)
    (he : e ∈ M.val) (hx : e.Incident x) : e=chosenEdge M x :=
  (Classical.choose_spec (M.property.2 x (Finset.mem_univ x))).2 e ⟨he,hx⟩

noncomputable def chosenMate (M : PM (BagEdge.Incident (bags := bags))) (x : V) : V :=
  Sym2.Mem.other (chosenEdge_spec M x).2

lemma chosenMate_pair (M : PM (BagEdge.Incident (bags := bags))) (x : V) :
    s(x,chosenMate M x)=(chosenEdge M x).val.val.1 := Sym2.other_spec _

lemma chosenMate_ne (M : PM (BagEdge.Incident (bags := bags))) (x : V) : chosenMate M x ≠ x :=
  Sym2.other_ne (chosenEdge M x).val.property _

lemma chosenEdge_chosenMate (M : PM (BagEdge.Incident (bags := bags))) (x : V) :
    chosenEdge M (chosenMate M x)=chosenEdge M x := by
  symm
  apply chosenEdge_unique M _ _ (chosenEdge_spec M x).1
  exact Sym2.other_mem (chosenEdge_spec M x).2

lemma chosenMate_involutive (M : PM (BagEdge.Incident (bags := bags))) :
    Function.Involutive (chosenMate M) := by
  intro x
  have h := chosenMate_pair M (chosenMate M x)
  rw [chosenEdge_chosenMate,←chosenMate_pair M x] at h
  rcases Sym2.eq_iff.mp h with h | h
  · exact False.elim (chosenMate_ne M x h.1)
  · exact h.2

noncomputable def fromPM (M : PM (BagEdge.Incident (bags := bags))) : ColoredPairing bags where
  pair := ⟨chosenMate M,chosenMate_involutive M,chosenMate_ne M⟩
  color x := (chosenEdge M x).val.color
  allowed x := (chosenEdge M x).property x (chosenEdge_spec M x).2
  same_color x := congrArg (fun e : BagEdge bags => e.val.color) (chosenEdge_chosenMate M x)

lemma fromPM_edgeAt (M : PM (BagEdge.Incident (bags := bags))) (x : V) :
    (fromPM M).edgeAt x=chosenEdge M x := by
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext (chosenMate_pair M x) rfl

lemma chosenEdge_toPM (p : ColoredPairing bags) (x : V) : chosenEdge p.toPM x=p.edgeAt x := by
  symm
  apply chosenEdge_unique
  · exact Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩
  · exact (p.edgeAt_incident x x).mpr (Or.inl rfl)

noncomputable def coloredPMEquiv : PM (BagEdge.Incident (bags := bags)) ≃ ColoredPairing bags where
  toFun := fromPM
  invFun := ColoredPairing.toPM
  left_inv M := by
    apply Subtype.ext
    ext e
    constructor
    · intro he
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp he
      rw [fromPM_edgeAt]
      exact (chosenEdge_spec M x).1
    · intro he
      obtain ⟨x,hx⟩ := e.exists_incident
      apply Finset.mem_image.mpr
      exact ⟨x,Finset.mem_univ _,(fromPM_edgeAt M x).trans (chosenEdge_unique M x e he hx).symm⟩
  right_inv p := by
    apply ColoredPairing.ext
    · ext x
      change chosenMate p.toPM x=p.pair.mate x
      have h := chosenMate_pair p.toPM x
      rw [chosenEdge_toPM] at h
      change s(x,chosenMate p.toPM x)=s(x,p.pair.mate x) at h
      exact Sym2.congr_right.mp h
    · funext x
      change (chosenEdge p.toPM x).val.color=p.color x
      rw [chosenEdge_toPM]
      rfl

theorem unit_partition_assignments :
    Fintype.card (PM (BagEdge.Incident (bags := bags))) =
      ∑ f : Assignment bags, ∏ l : L, pairingCount (Fintype.card {x : V // f.val x=l}) := by
  classical
  rw [Fintype.card_congr (coloredPMEquiv (bags := bags)),coloredPairing_card]



open Finset

variable {U S W L : Type*} [Fintype U] [Fintype S] [Fintype W] [Fintype L]
  [DecidableEq U] [DecidableEq S] [DecidableEq W] [DecidableEq L]

def leafBags (l p : L) (b : W → Finset L) : U ⊕ S ⊕ W → Finset L
  | Sum.inl _ => {l}
  | Sum.inr (Sum.inl _) => {l,p}
  | Sum.inr (Sum.inr x) => b x

noncomputable def fiberCount {V : Type*} [Fintype V] (f : V → L) (l : L) : ℕ :=
  Fintype.card {x : V // f x=l}

noncomputable def assignmentPartition {V : Type*} [Fintype V] [DecidableEq V]
    (b : V → Finset L) (w : L → ℕ → ℕ) : ℕ :=
  by classical exact ∑ f : Assignment b, ∏ l,w l (fiberCount f.val l)

def leafAssignment (l p : L) (b : W → Finset L) (T : Finset S) (f : Assignment b) :
    Assignment (leafBags (U := U) (S := S) l p b) :=
  ⟨Sum.elim (fun _ => l) (Sum.elim (fun x => if x∈T then l else p) f.val),by
    intro x
    rcases x with x | (x | x)
    · simp [leafBags]
    · by_cases hx : x∈T <;> simp [leafBags,hx]
    · exact f.property x⟩

noncomputable def leafAssignmentEquiv (l p : L) (hlp : l≠p) (b : W → Finset L) :
    Assignment (leafBags (U := U) (S := S) l p b) ≃ (Finset S) × Assignment b where
  toFun f := (univ.filter fun x => f.val (Sum.inr (Sum.inl x))=l,
    ⟨fun x => f.val (Sum.inr (Sum.inr x)),fun x => f.property _⟩)
  invFun q := leafAssignment l p b q.1 q.2
  left_inv f := by
    apply Subtype.ext
    funext x
    rcases x with x | (x | x)
    · have hf := f.property (Sum.inl x)
      have hfl : f.val (Sum.inl x)=l := by simpa [leafBags] using hf
      simpa [leafAssignment] using hfl.symm
    · by_cases h : f.val (Sum.inr (Sum.inl x))=l
      · simp [leafAssignment,h]
      · have hf := f.property (Sum.inr (Sum.inl x))
        simp only [leafBags,mem_insert,mem_singleton] at hf
        simp [leafAssignment,hf.resolve_left h,hlp.symm]
    · rfl
  right_inv q := by
    apply Prod.ext
    · ext x
      by_cases hx : x∈q.1 <;> simp [leafAssignment,hx,hlp.symm]
    · rfl

omit [Fintype L] in
lemma fiberCount_sum [Fintype L] {A B : Type*} [Fintype A] [Fintype B] (f : A ⊕ B → L) (l : L) :
    fiberCount f l = fiberCount (fun x : A => f (Sum.inl x)) l +
      fiberCount (fun x : B => f (Sum.inr x)) l := by
  unfold fiberCount
  rw [Fintype.card_congr Equiv.subtypeSum,Fintype.card_sum]

omit [Fintype L] [DecidableEq U] in
lemma fiberCount_const [Fintype L] [DecidableEq U]
    (a l : L) : fiberCount (fun _ : U => a) l = if a=l then Fintype.card U else 0 := by
  classical
  by_cases h : a=l <;> simp [fiberCount,h]

omit [Fintype L] in
lemma fiberCount_zero [Fintype L] {A : Type*} [Fintype A] (f : A → L) (l : L) (h : ∀ x,f x≠l) :
    fiberCount f l=0 := by
  classical
  simp [fiberCount,h]

omit [DecidableEq W] in
lemma fiberCount_leaf [DecidableEq W] (l p : L) (hlp : l≠p) (b : W → Finset L)
    (hb : ∀ x,l∉b x) (T : Finset S) (f : Assignment b) :
    fiberCount (leafAssignment (U := U) l p b T f).val l = Fintype.card U+T.card := by
  rw [fiberCount_sum,fiberCount_sum]
  have hz : fiberCount f.val l=0 := fiberCount_zero _ _ (fun x h => hb x (h ▸ f.property x))
  change fiberCount (fun _ : U => l) l +
    (fiberCount (fun x : S => if x∈T then l else p) l + fiberCount f.val l)=_
  rw [fiberCount_const,ite_eq_left rfl,hz,Nat.add_zero]
  congr 1
  unfold fiberCount
  rw [Fintype.card_congr (Equiv.subtypeEquivRight (q := fun x => x∈T) (fun x => by simp [hlp.symm]))]
  exact Fintype.card_coe T

omit [DecidableEq W] in
lemma fiberCount_parent [DecidableEq W] (l p : L) (hlp : l≠p) (b : W → Finset L)
    (T : Finset S) (f : Assignment b) :
    fiberCount (leafAssignment (U := U) l p b T f).val p =
      Fintype.card S-T.card+fiberCount f.val p := by
  rw [fiberCount_sum,fiberCount_sum]
  change fiberCount (fun _ : U => l) p +
    (fiberCount (fun x : S => if x∈T then l else p) p + fiberCount f.val p)=_
  rw [fiberCount_const,ite_eq_right hlp,Nat.zero_add]
  congr 1
  unfold fiberCount
  rw [Fintype.card_congr (Equiv.subtypeEquivRight (q := fun x => x∉T) (fun x => by simp [hlp]))]
  rw [Fintype.card_subtype_compl,Fintype.card_coe]

omit [DecidableEq W] in
lemma fiberCount_other [DecidableEq W] (l p a : L) (hal : a≠l) (hap : a≠p) (b : W → Finset L)
    (T : Finset S) (f : Assignment b) :
    fiberCount (leafAssignment (U := U) l p b T f).val a = fiberCount f.val a := by
  rw [fiberCount_sum,fiberCount_sum]
  change fiberCount (fun _ : U => l) a +
    (fiberCount (fun x : S => if x∈T then l else p) a + fiberCount f.val a)=_
  rw [fiberCount_const,ite_eq_right hal.symm]
  have hz : fiberCount (fun x : S => if x∈T then l else p) a=0 := by
    apply fiberCount_zero
    intro x
    split_ifs
    · exact hal.symm
    · exact hap.symm
  simp [hz]

lemma prod_split_two (l p : L) (hlp : l≠p) (f : L → ℕ) :
    (∏ a,f a)=f l*f p*(∏ a∈(univ.erase l).erase p,f a) := by
  rw [←prod_erase_mul univ f (mem_univ l),
    ←prod_erase_mul (univ.erase l) f (mem_erase.mpr ⟨hlp.symm,mem_univ p⟩)]
  ac_rfl

lemma leaf_assignment_weight (l p : L) (hlp : l≠p) (b : W → Finset L)
    (hb : ∀ x,l∉b x) (w : L → ℕ → ℕ) (T : Finset S) (f : Assignment b) :
    (∏ a,w a (fiberCount (leafAssignment (U := U) l p b T f).val a)) =
      w l (Fintype.card U+T.card) * w p (Fintype.card S-T.card+fiberCount f.val p) *
        (∏ a∈(univ.erase l).erase p,w a (fiberCount f.val a)) := by
  rw [prod_split_two l p hlp,fiberCount_leaf l p hlp b hb,fiberCount_parent l p hlp]
  congr 1
  apply prod_congr rfl
  intro a ha
  rw [fiberCount_other _ _ _ (mem_erase.mp (mem_erase.mp ha).2).1 (mem_erase.mp ha).1]

omit [DecidableEq S] in
lemma sum_finset_card [DecidableEq S] (g : ℕ → ℕ) :
    (∑ T : Finset S,g T.card)=∑ k∈range (Fintype.card S+1),(Fintype.card S).choose k*g k := by
  classical
  have hu : (univ : Finset (Finset S))=(univ : Finset S).powerset := by ext T; simp
  rw [hu,sum_powerset]
  apply sum_congr rfl
  intro k hk
  simpa using (sum_powersetCard k (univ : Finset S) g)

noncomputable def leafUpdate (u s : ℕ) (l p : L) (w : L → ℕ → ℕ) : L → ℕ → ℕ :=
  fun a r => if a=l then 1 else if a=p then
    ∑ k∈range (s+1),s.choose k*w l (u+k)*w p (s-k+r) else w a r

theorem leaf_elimination (l p : L) (hlp : l≠p) (b : W → Finset L)
    (hb : ∀ x,l∉b x) (w : L → ℕ → ℕ) :
    assignmentPartition (leafBags (U := U) (S := S) l p b) w =
      assignmentPartition b (leafUpdate (Fintype.card U) (Fintype.card S) l p w) := by
  classical
  unfold assignmentPartition
  calc
    _ = ∑ q : Finset S × Assignment b,
        ∏ a,w a (fiberCount (leafAssignment (U := U) l p b q.1 q.2).val a) := by
      apply Fintype.sum_equiv (leafAssignmentEquiv l p hlp b)
      intro f
      exact congrArg (fun q : Assignment (leafBags (U := U) (S := S) l p b) =>
        ∏ a,w a (fiberCount q.val a)) ((leafAssignmentEquiv l p hlp b).left_inv f).symm
    _ = _ := by
      rw [Fintype.sum_prod_type,sum_comm]
      apply sum_congr rfl
      intro f hf
      simp_rw [leaf_assignment_weight l p hlp b hb w]
      rw [sum_finset_card (S:=S) (fun k =>
        w l (Fintype.card U+k)*w p (Fintype.card S-k+fiberCount f.val p)*
        (∏ a∈(univ.erase l).erase p,w a (fiberCount f.val a)))]
      rw [prod_split_two l p hlp]
      have he : (∏ a∈(univ.erase l).erase p,
          leafUpdate (Fintype.card U) (Fintype.card S) l p w a (fiberCount f.val a)) =
          ∏ a∈(univ.erase l).erase p,w a (fiberCount f.val a) := by
        apply prod_congr rfl
        intro a ha
        simp only [leafUpdate,ite_eq_right (mem_erase.mp (mem_erase.mp ha).2).1,
          ite_eq_right (mem_erase.mp ha).1]
      rw [he]
      simp only [leafUpdate,ite_true,ite_eq_right hlp.symm,one_mul]
      rw [sum_mul]
      apply sum_congr rfl
      intro k hk
      ac_rfl

end MatchingFPRAS.UnitRefresh

end OAI
