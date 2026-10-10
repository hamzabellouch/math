import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingListActual
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListPathMatrix

namespace OAI

/-! Exact full-space matrix semantics for the computed crossing packet.
The nine serialized bonds are the nine physical edges of each crossing. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingListLayer
open QuantumCrossingListBlock MediatorGraph
open scoped BigOperators Classical

def edgeTag {r : ℕ} (C : QMARationalCrossingLayer r) (N : ℚ)
    (i : Fin r) : Fin 9 → (C.output N).Edge :=
  ![.inl (.inr (i,0)),.inl (.inr (i,1)),.inl (.inr (i,2)),.inl (.inr (i,3)),
    .inr (.inl i),.inr (.inr (i,0)),.inr (.inr (i,1)),
    .inr (.inr (i,2)),.inr (.inr (i,3))]

private theorem fresh_value (n r : ℕ) (i : Fin r) (a : Fin 2) :
    (fresh n r i a).val=n+2*i.val+a.val := by
  change n+(a.val+2*i.val)=_
  omega

private theorem old_value (n r : ℕ) (i : Fin n) : (old n r i).val=i.val := rfl

theorem bond_actual {r : ℕ} (C : QMARationalCrossingLayer r) (N : ℚ)
    (i : Fin r) (k : Fin 9) :
    bond ((C.base.n,C.scale N),i.val,actualCrossing C i) k =
      (((C.output N).left (edgeTag C N i k)).val,
        ((C.output N).right (edgeTag C N i k)).val,
        (C.output N).weight (edgeTag C N i k)) := by
  fin_cases k <;>
    simp [bond,left,right,coefficient,base,actualCrossing,site,edgeTag,
      QMARationalCrossingLayer.output,qmaParallelGraphLeft,qmaParallelGraphRight,
      qmaCrossingsBaseLeft,qmaCrossingsBaseRight,qmaCrossingLeft,qmaCrossingRight,
      qmaCrossingMember,fresh_value,old_value]

theorem block_matrix_actual {r : ℕ} (C : QMARationalCrossingLayer r) (N : ℚ)
    (i : Fin r) :
    SourceBondLists.matrix (C.output N).n
      (block ((C.base.n,C.scale N),i.val,actualCrossing C i)) =
      ∑ k : Fin 9, ((C.output N).weight (edgeTag C N i k):ℂ) •
        sourceHeisenbergMatrix (C.output N).n
          ((C.output N).left (edgeTag C N i k)) ((C.output N).right (edgeTag C N i k)) := by
  simp only [SourceBondLists.matrix,block,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [bond_actual,SourceBondLists.bondMatrix,dite_eq_left
    ⟨((C.output N).left (edgeTag C N i k)).isLt,
      ((C.output N).right (edgeTag C N i k)).isLt⟩]

private theorem indexed_ofFn {r : ℕ} (p : Parameters) (f : Fin r → Crossing)
    (i : Fin r) : indexed (i.val,(p,List.ofFn f))=(p,i.val,f i) := by
  unfold indexed
  rw [List.headD_eq_head?_getD,List.head?_drop,
    List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using i.isLt)]
  simp only [List.getElem_ofFn,Option.getD_some]

theorem family_ofFn {r : ℕ} (p : Parameters) (f : Fin r → Crossing) :
    family (p,List.ofFn f)=(List.ofFn fun i => block (p,i.val,f i)).flatten := by
  have hr (g : ℕ → List MediatorListProgram.Bond) :
      (List.range r).map g=List.ofFn (fun i : Fin r => g i.val) := by
    simpa only [List.length_range,List.getElem_range,Fin.val_cast] using
      (List.ofFn_getElem_eq_map (List.range r) g).symm
  unfold family
  rw [List.length_ofFn,hr]
  apply congrArg List.flatten
  apply congrArg (fun g : Fin r → List MediatorListProgram.Bond => List.ofFn g)
  funext i
  rw [indexed_ofFn]

theorem family_matrix_actual {r : ℕ} (C : QMARationalCrossingLayer r) (N : ℚ) :
    SourceBondLists.matrix (C.output N).n
      (family ((C.base.n,C.scale N),List.ofFn (actualCrossing C))) =
      ∑ i : Fin r, ∑ k : Fin 9, ((C.output N).weight (edgeTag C N i k):ℂ) •
        sourceHeisenbergMatrix (C.output N).n
          ((C.output N).left (edgeTag C N i k)) ((C.output N).right (edgeTag C N i k)) := by
  rw [family_ofFn,QuantumListPathProgram.matrix_flatten]
  simp only [List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  exact Finset.sum_congr rfl (fun i _ => block_matrix_actual C N i)

theorem edgeTag_sum {r : ℕ} (C : QMARationalCrossingLayer r) (N : ℚ)
    {V : Type*} [AddCommMonoid V] (f : (C.output N).Edge → V) (i : Fin r) :
    (∑ k : Fin 9, f (edgeTag C N i k)) =
      (∑ a : Fin 4, f (.inl (.inr (i,a))))+f (.inr (.inl i))+
        ∑ a : Fin 4, f (.inr (.inr (i,a))) := by
  simp [Fin.sum_univ_succ,edgeTag,add_assoc]

private theorem sum_crossing_edges {α V : Type*} [Fintype α] [AddCommMonoid V]
    {r : ℕ} (f : ((α ⊕ (Fin r × Fin 4)) ⊕ (Fin r ⊕ (Fin r × Fin 4))) → V) :
    (∑ e, f e) = (∑ e : α, f (.inl (.inl e)))+
      (∑ i : Fin r, ((∑ a : Fin 4, f (.inl (.inr (i,a))))+
        f (.inr (.inl i))+(∑ a : Fin 4, f (.inr (.inr (i,a)))))) := by
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,Finset.sum_add_distrib]
  ac_rfl

theorem matrix_actual {r : ℕ} (C : QMARationalCrossingLayer r) (N : ℚ) {m : ℕ}
    (labels : C.base.Edge ≃ Fin m) :
    SourceBondLists.matrix (C.output N).n (bonds (actualInput C N labels))+
      ((C.output N).constant:ℂ) • 1 =
      qmaExchangeMatrix (C.output N).left (C.output N).right
        (fun e => ((C.output N).weight e:ℝ)) (C.output N).constant := by
  let f : (C.output N).Edge →
      Matrix (SourceSpinBasis (C.output N).n) (SourceSpinBasis (C.output N).n) ℂ :=
    fun e => ((C.output N).weight e:ℂ) • sourceHeisenbergMatrix (C.output N).n
      ((C.output N).left e) ((C.output N).right e)
  have hb : SourceBondLists.matrix (C.output N).n (QuantumListGraph.packed C.base labels) =
      ∑ e : C.base.Edge, f (.inl (.inl e)) := by
    change SourceBondLists.matrix (C.base.n+r*2)
      (List.ofFn fun i => ((C.base.left (labels.symm i)).val,
        (C.base.right (labels.symm i)).val,C.base.weight (labels.symm i))) = _
    rw [QuantumListPathProgram.retained_matrix]
    exact labels.symm.sum_comp (fun e => (C.base.weight e:ℂ) •
      sourceHeisenbergMatrix (C.base.n+r*2)
        (old C.base.n r (C.base.left e)) (old C.base.n r (C.base.right e)))
  have hfamily : familyInput (actualInput C N labels) =
      ((C.base.n,C.scale N),List.ofFn (actualCrossing C)) := by
    unfold familyInput
    rw [parameters_actual]
    rfl
  unfold bonds
  simp only [SourceBondLists.matrix,List.map_append,List.sum_append]
  change (SourceBondLists.matrix (C.output N).n (QuantumListGraph.packed C.base labels)+
    SourceBondLists.matrix (C.output N).n (family (familyInput (actualInput C N labels))))+_ = _
  rw [hfamily,hb,family_matrix_actual]
  change ((∑ e : C.base.Edge, f (.inl (.inl e)))+
    ∑ i : Fin r, ∑ k : Fin 9, f (edgeTag C N i k))+_ = _
  have ht : (∑ i : Fin r, ∑ k : Fin 9, f (edgeTag C N i k)) =
      ∑ i : Fin r, ((∑ a : Fin 4, f (.inl (.inr (i,a))))+
        f (.inr (.inl i))+(∑ a : Fin 4, f (.inr (.inr (i,a))))) :=
    Finset.sum_congr rfl (fun i _ => edgeTag_sum C N f i)
  rw [ht]
  have hf : (∑ e, f e) = (∑ e : C.base.Edge, f (.inl (.inl e)))+
      (∑ i : Fin r, ((∑ a : Fin 4, f (.inl (.inr (i,a))))+
        f (.inr (.inl i))+(∑ a : Fin 4, f (.inr (.inr (i,a)))))) := by
    exact sum_crossing_edges (α := C.base.Edge) f
  simp only [qmaExchangeMatrix,Complex.ofReal_ratCast]
  exact congrArg (fun x => x+((C.output N).constant:ℂ) • 1) hf.symm

theorem energy_actual {r : ℕ} (C : QMARationalCrossingLayer r) (N : ℚ) {m : ℕ}
    (labels : C.base.Edge ≃ Fin m) : (actualGraph C N labels).energy=(C.output N).energy := by
  unfold actualGraph graph
  rw [QuantumListGraph.ofBonds_energy,count_actual,constant_actual]
  exact congrArg (sourceMatrixBottom (C.output N).n) (matrix_actual C N labels)

theorem energy_error {r : ℕ} (C : QMARationalCrossingLayer r) {N : ℚ} (hN : 0 < N)
    {m : ℕ} (labels : C.base.Edge ≃ Fin m) :
    |(actualGraph C N labels).energy-C.source.energy| ≤ 1/(N:ℝ) := by
  rw [energy_actual]
  exact C.output_energy_error hN

end ContinuumCoulomb.QuantumCrossingListLayer

end

end OAI
