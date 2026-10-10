import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListScheduleLabels

namespace OAI

/-! Exact edge order in the emitted next-round list: retained edges followed
by three consecutive edges for each selected source edge. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListSchedule
open MediatorListProgram

abbrev Tags (x : Input) := Fin (partition false x.2.2.2).length ⊕
  (Fin (partition true x.2.2.2).length × Fin 3)

def tagValue (x : Input) : Tags x → Entry
  | .inl i => (partition false x.2.2.2).get i
  | .inr (i,k) => (blockWork (indexed (i.val,x)) k,
      QuantumListPathProgram.bond (blockBondInput (indexed (i.val,x))) k)

def flatTagEquiv (x : Input) :
    Fin ((partition false x.2.2.2).length+(partition true x.2.2.2).length*3) ≃ Tags x :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl _) finProdFinEquiv.symm)

theorem family_ofFn (x : Input) : family x =
    (List.ofFn fun i : Fin (partition true x.2.2.2).length => block (indexed (i.val,x))).flatten := by
  have h : (List.range (partition true x.2.2.2).length).map (fun i => block (indexed (i,x))) =
      List.ofFn (fun i : Fin (partition true x.2.2.2).length => block (indexed (i.val,x))) := by
    simpa only [List.length_range,List.getElem_range,Fin.val_cast] using
      (List.ofFn_getElem_eq_map (List.range (partition true x.2.2.2).length)
        (fun i => block (indexed (i,x)))).symm
  exact congrArg List.flatten h

private theorem ofFn_triples {m : ℕ} (f : Fin m × Fin 3 → Entry) :
    List.ofFn (fun k : Fin (m*3) => f (finProdFinEquiv.symm k)) =
      (List.ofFn fun i : Fin m => List.ofFn fun k : Fin 3 => f (i,k)).flatten := by
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg (fun g : Fin m → List Entry => List.ofFn g)
  funext i
  apply congrArg (fun g : Fin 3 → Entry => List.ofFn g)
  funext k
  have he : (⟨i.val*3+k.val,by omega⟩ : Fin (m*3))=finProdFinEquiv (i,k) := by
    apply Fin.ext
    change i.val*3+k.val=k.val+3*i.val
    omega
  rw [he,Equiv.symm_apply_apply]

theorem value_ofFn (x : Input) :
    (value x).2.2 = List.ofFn (fun i => tagValue x (flatTagEquiv x i)) := by
  rw [List.ofFn_add]
  change _ = (List.ofFn (fun i : Fin (partition false x.2.2.2).length =>
    tagValue x (flatTagEquiv x (Fin.castAdd ((partition true x.2.2.2).length*3) i))))++
    List.ofFn (fun i : Fin ((partition true x.2.2.2).length*3) =>
      tagValue x (flatTagEquiv x (Fin.natAdd (partition false x.2.2.2).length i)))
  simp only [flatTagEquiv,Equiv.trans_apply,finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd,Equiv.sumCongr_apply,Equiv.refl_apply,
    Sum.map_inl,Sum.map_inr,tagValue]
  rw [List.ofFn_get]
  have h3 := ofFn_triples (fun p : Fin (partition true x.2.2.2).length × Fin 3 =>
    (blockWork (indexed (p.1.val,x)) p.2,
      QuantumListPathProgram.bond (blockBondInput (indexed (p.1.val,x))) p.2))
  rw [h3]
  change partition false x.2.2.2++family x = _
  rw [family_ofFn]
  rfl

theorem value_length (x : Input) : (value x).2.2.length =
    (partition false x.2.2.2).length+(partition true x.2.2.2).length*3 := by
  change (partition false x.2.2.2++family x).length = _
  rw [List.length_append,family_length]

def tagEquiv (x : Input) : Fin (value x).2.2.length ≃ Tags x :=
  (finCongr (value_length x)).trans (flatTagEquiv x)

theorem tagEquiv_get (x : Input) (i : Fin (value x).2.2.length) :
    (value x).2.2.get i=tagValue x (tagEquiv x i) := by
  have hi : i.val<(partition false x.2.2.2).length+(partition true x.2.2.2).length*3 := by
    rw [← value_length]
    exact i.isLt
  have h := congrArg (fun xs : List Entry => xs[i.val]?) (value_ofFn x)
  have hc : Fin.cast (value_length x) i = ⟨i.val,hi⟩ := Fin.ext rfl
  change (value x).2.2.get i = tagValue x (flatTagEquiv x (Fin.cast (value_length x) i))
  rw [hc]
  simpa only [List.getElem?_eq_getElem i.isLt,List.getElem?_ofFn,dite_eq_left hi,
    Option.some.injEq,List.get_eq_getElem] using h

end ContinuumCoulomb.QuantumListSchedule

end

end OAI
