import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListScheduleOrder
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathRelabelingProperties

namespace OAI

/-! The exact emitted edge order realizes the abstract scheduled subdivision.
This transfers the disjoint-route invariant to the literal list compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListSchedule
open MediatorGraph
open scoped Classical

private def role {a b : ℕ} (e : Fin a ≃ Fin b) (p : Fin a × Fin 3) :
    Fin b ⊕ (Fin b × Fin 2) :=
  ![.inl (e p.1),.inr (e p.1,0),.inr (e p.1,1)] p.2

private def unrole {a b : ℕ} (e : Fin a ≃ Fin b) :
    Fin b ⊕ (Fin b × Fin 2) → Fin a × Fin 3
  | .inl i => (e.symm i,0)
  | .inr (i,k) => (e.symm i,k.succ)

private def roleEquiv {a b : ℕ} (e : Fin a ≃ Fin b) :
    (Fin a × Fin 3) ≃ (Fin b ⊕ (Fin b × Fin 2)) where
  toFun := role e
  invFun := unrole e
  left_inv := by
    rintro ⟨i,k⟩
    fin_cases k <;> simp [role,unrole]
  right_inv := by
    rintro (i | ⟨i,k⟩)
    · simp [role,unrole]
    · fin_cases k <;> simp [role,unrole]

private theorem oldValue (n r : ℕ) (i : Fin n) : (old n r i).val=i.val := rfl
private theorem freshValue (n r : ℕ) (i : Fin r) (a : Fin 2) :
    (fresh n r i a).val=n+2*i.val+a.val := by
  change n+(a.val+2*i.val)=_
  omega

def nextEdge (x : Input) (hs : Valid x.2) :
    (schedule (value x) (value_valid x hs)).graph.Edge ≃
      ((schedule x.2 hs).next x.1).graph.Edge :=
  (tagEquiv x).trans (Equiv.sumCongr (retainedEquiv x.2 hs)
    (roleEquiv (activePermutation x.2 hs)))

theorem value_count (x : Input) :
    (value x).1=x.2.1+(partition true x.2.2.2).length*2 := by
  simp only [value,QuantumListPathStep.count,stepInput,erase,List.length_map]

def nextVertex (x : Input) (hs : Valid x.2) :
    Fin (schedule (value x) (value_valid x hs)).graph.n ≃
      Fin ((schedule x.2 hs).next x.1).graph.n :=
  (finCongr (value_count x)).trans (vertexRelabel x.2 hs)

private theorem indexed_entry (x : Input) (i : Fin (partition true x.2.2.2).length) :
    (indexed (i.val,x)).2.2=(partition true x.2.2.2).get i := by
  change ((partition true x.2.2.2).drop i.val).headD zeroEntry = _
  rw [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_eq_getElem i.isLt]
  rfl

private theorem indexed_bond (x : Input) (i : Fin (partition true x.2.2.2).length) :
    blockBondInput (indexed (i.val,x)) =
      (QuantumListPathStep.parameters (stepInput x),i.val,((partition true x.2.2.2).get i).2) := by
  change (QuantumListPathStep.parameters (stepInput x),i.val,(indexed (i.val,x)).2.2.2) = _
  rw [indexed_entry]

private def tagLeft (x : Input) (hs : Valid x.2) : Tags x →
    Fin (x.2.1+(partition true x.2.2.2).length*2)
  | .inl i => old _ _ ((graph x.2 hs).left (retainedEquiv x.2 hs i).val)
  | .inr (i,k) => ![fresh _ _ i 0,
      old _ _ ((graph x.2 hs).left (qmaSelectedIndex (schedule x.2 hs).active (activePermutation x.2 hs i))),
      old _ _ ((graph x.2 hs).right (qmaSelectedIndex (schedule x.2 hs).active (activePermutation x.2 hs i)))] k

private def tagRight (x : Input) (hs : Valid x.2) : Tags x →
    Fin (x.2.1+(partition true x.2.2.2).length*2)
  | .inl i => old _ _ ((graph x.2 hs).right (retainedEquiv x.2 hs i).val)
  | .inr (i,k) => ![fresh _ _ i 1,fresh _ _ i 0,fresh _ _ i 1] k

private theorem left_tag (x : Input) (hs : Valid x.2) (t : Tags x) :
    finCongr (value_count x)
        ((graph (value x) (value_valid x hs)).left ((tagEquiv x).symm t)) =
      tagLeft x hs t := by
  apply Fin.ext
  change ((value x).2.2.get ((tagEquiv x).symm t)).2.1 = _
  rw [tagEquiv_get,Equiv.apply_symm_apply]
  rcases t with i | ⟨i,k⟩
  · change ((partition false x.2.2.2).get i).2.1 = _
    simpa only [tagLeft,oldValue,graph] using
      (congrArg (fun e : Entry => e.2.1) (retained_source x.2 hs i)).symm
  · have he := active_source x.2 hs i
    simp only [List.get_eq_getElem] at he
    fin_cases k <;>
      simp [tagValue,tagLeft,QuantumListPathProgram.bond,QuantumListPathProgram.left,
        indexed_bond,QuantumListPathStep.parameters,stepInput,graph,
        oldValue,freshValue,he]

private theorem right_tag (x : Input) (hs : Valid x.2) (t : Tags x) :
    finCongr (value_count x)
        ((graph (value x) (value_valid x hs)).right ((tagEquiv x).symm t)) =
      tagRight x hs t := by
  apply Fin.ext
  change ((value x).2.2.get ((tagEquiv x).symm t)).2.2.1 = _
  rw [tagEquiv_get,Equiv.apply_symm_apply]
  rcases t with i | ⟨i,k⟩
  · change ((partition false x.2.2.2).get i).2.2.1 = _
    simpa only [tagRight,oldValue,graph] using
      (congrArg (fun e : Entry => e.2.2.1) (retained_source x.2 hs i)).symm
  · fin_cases k <;>
      simp [tagValue,tagRight,QuantumListPathProgram.bond,QuantumListPathProgram.right,
        indexed_bond,QuantumListPathStep.parameters,stepInput,
        freshValue]

def tagEdge (x : Input) (hs : Valid x.2) : Tags x →
    QMAPartialPathsEdge (schedule x.2 hs).active
  | .inl i => .inl (retainedEquiv x.2 hs i)
  | .inr p => .inr (role (activePermutation x.2 hs) p)

private theorem nextEdge_eq (x : Input) (hs : Valid x.2) (i : Fin (value x).2.2.length) :
    nextEdge x hs i=tagEdge x hs (tagEquiv x i) := by
  change (Equiv.sumCongr (retainedEquiv x.2 hs)
    (roleEquiv (activePermutation x.2 hs))) (tagEquiv x i) = _
  generalize tagEquiv x i=t
  rcases t with i | ⟨i,k⟩ <;> rfl

theorem nextEdge_tag (x : Input) (hs : Valid x.2) (t : Tags x) :
    nextEdge x hs ((tagEquiv x).symm t) = tagEdge x hs t := by
  have h := nextEdge_eq x hs ((tagEquiv x).symm t)
  simpa only [Equiv.apply_symm_apply] using h

private theorem tag_left_relabel (x : Input) (hs : Valid x.2) (t : Tags x) :
    vertexRelabel x.2 hs (tagLeft x hs t) =
      ((schedule x.2 hs).next x.1).graph.left (tagEdge x hs t) := by
  rcases t with i | ⟨i,k⟩
  · exact vertexRelabel_old _ _ _
  · fin_cases k
    · exact vertexRelabel_fresh _ _ _ _
    · exact vertexRelabel_old _ _ _
    · exact vertexRelabel_old _ _ _

private theorem tag_right_relabel (x : Input) (hs : Valid x.2) (t : Tags x) :
    vertexRelabel x.2 hs (tagRight x hs t) =
      ((schedule x.2 hs).next x.1).graph.right (tagEdge x hs t) := by
  rcases t with i | ⟨i,k⟩
  · exact vertexRelabel_old _ _ _
  · fin_cases k
    · exact vertexRelabel_fresh _ _ _ _
    · exact vertexRelabel_fresh _ _ _ _
    · exact vertexRelabel_fresh _ _ _ _

private theorem work_tag (x : Input) (hs : Valid x.2) (t : Tags x) :
    (tagValue x t).1=((schedule x.2 hs).next x.1).work (tagEdge x hs t) := by
  rcases t with i | ⟨i,k⟩
  · exact partition_zero _ _ (List.get_mem _ i)
  · fin_cases k
    · rfl
    · rfl
    · change (indexed (i.val,x)).2.2.1-1 =
        (x.2.2.2.get (qmaSelectedIndex (schedule x.2 hs).active (activePermutation x.2 hs i))).1-1
      rw [indexed_entry]
      exact congrArg (fun e : Entry => e.1-1) (active_source x.2 hs i).symm

private theorem next_left (x : Input) (hs : Valid x.2) (i : Fin (value x).2.2.length) :
    nextVertex x hs ((graph (value x) (value_valid x hs)).left i) =
      ((schedule x.2 hs).next x.1).graph.left (nextEdge x hs i) := by
  rw [nextEdge_eq]
  have h : finCongr (value_count x) ((graph (value x) (value_valid x hs)).left i) =
      tagLeft x hs (tagEquiv x i) := by
    simpa only [Equiv.symm_apply_apply] using left_tag x hs (tagEquiv x i)
  exact (congrArg (vertexRelabel x.2 hs) h).trans (tag_left_relabel x hs (tagEquiv x i))

private theorem next_right (x : Input) (hs : Valid x.2) (i : Fin (value x).2.2.length) :
    nextVertex x hs ((graph (value x) (value_valid x hs)).right i) =
      ((schedule x.2 hs).next x.1).graph.right (nextEdge x hs i) := by
  rw [nextEdge_eq]
  have h : finCongr (value_count x) ((graph (value x) (value_valid x hs)).right i) =
      tagRight x hs (tagEquiv x i) := by
    simpa only [Equiv.symm_apply_apply] using right_tag x hs (tagEquiv x i)
  exact (congrArg (vertexRelabel x.2 hs) h).trans (tag_right_relabel x hs (tagEquiv x i))

private theorem next_work (x : Input) (hs : Valid x.2) (i : Fin (value x).2.2.length) :
    (schedule (value x) (value_valid x hs)).work i =
      ((schedule x.2 hs).next x.1).work (nextEdge x hs i) := by
  change ((value x).2.2.get i).1 = _
  rw [tagEquiv_get,nextEdge_eq]
  exact work_tag x hs (tagEquiv x i)

def nextRelabel (x : Input) (hs : Valid x.2) :
    QMAPathRelabeling (schedule (value x) (value_valid x hs))
      ((schedule x.2 hs).next x.1) where
  vertex := nextVertex x hs
  edge := nextEdge x hs
  left := next_left x hs
  right := next_right x hs
  work := next_work x hs

end ContinuumCoulomb.QuantumListSchedule

end

end OAI
