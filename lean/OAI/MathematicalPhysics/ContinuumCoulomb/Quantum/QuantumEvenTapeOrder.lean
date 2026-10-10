import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumEvenTapeProgram

namespace OAI

/-! The exact three-entry order of the literal even-subdivision output. -/

noncomputable section
namespace ContinuumCoulomb.QuantumEvenTapeProgram
open QuantumListSchedule
open scoped Classical

abbrev Tags (x : Input) := Fin x.2.1.2.1.length × Fin 3
def tagValue (x : Input) (t : Tags x) : Entry :=
  (blockWork (blockInput (t.1.val,x)) t.2,
    QuantumListPathProgram.bond (blockBondInput (blockInput (t.1.val,x))) t.2)

theorem entries_nested (x : Input) : entries x=
    (List.ofFn (fun i : Fin x.2.1.2.1.length => block (blockInput (i.val,x)))).flatten := by
  apply congrArg List.flatten
  simpa only [List.length_range,List.getElem_range,Fin.val_cast] using
    (List.ofFn_getElem_eq_map (List.range x.2.1.2.1.length)
      (fun i => block (blockInput (i,x)))).symm

private theorem ofFn_triples {m : ℕ} (f : Fin m × Fin 3 → Entry) :
    List.ofFn (fun k : Fin (m*3) => f (finProdFinEquiv.symm k))=
      (List.ofFn (fun i : Fin m => List.ofFn (fun k : Fin 3 => f (i,k)))).flatten := by
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext k
  have he : (⟨i.val*3+k.val,by omega⟩ : Fin (m*3))=finProdFinEquiv (i,k) := by
    apply Fin.ext
    change i.val*3+k.val=k.val+3*i.val
    omega
  rw [he,Equiv.symm_apply_apply]

theorem entries_ofFn (x : Input) : entries x=
    List.ofFn (fun i : Fin (x.2.1.2.1.length*3) => tagValue x (finProdFinEquiv.symm i)) := by
  rw [ofFn_triples,entries_nested]
  rfl

theorem entries_length (x : Input) : (entries x).length=x.2.1.2.1.length*3 := by
  rw [entries_ofFn,List.length_ofFn]

def tagEquiv (x : Input) : Fin (entries x).length ≃ Tags x :=
  (finCongr (entries_length x)).trans finProdFinEquiv.symm

theorem tagEquiv_get (x : Input) (i : Fin (entries x).length) :
    (entries x).get i=tagValue x (tagEquiv x i) := by
  have hi : i.val<x.2.1.2.1.length*3 := by rw [← entries_length]; exact i.isLt
  have h := congrArg (fun xs : List Entry => xs[i.val]?) (entries_ofFn x)
  have hc : Fin.cast (entries_length x) i=⟨i.val,hi⟩ := Fin.ext rfl
  change (entries x).get i=tagValue x (finProdFinEquiv.symm (Fin.cast (entries_length x) i))
  rw [hc]
  simpa only [List.getElem?_eq_getElem i.isLt,List.getElem?_ofFn,dite_eq_left hi,
    Option.some.injEq,List.get_eq_getElem] using h

end ContinuumCoulomb.QuantumEvenTapeProgram

end

end OAI
