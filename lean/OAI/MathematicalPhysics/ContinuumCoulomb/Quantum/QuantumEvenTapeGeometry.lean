import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumEvenRouteLabels
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPackedSchedule
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPlanarRouteRealization
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFinalRoutingProgram

namespace OAI

/-! The literal even tape has the canonical reserved-leaf geometry, up to
its explicit vertex and triple-edge ordering. -/

noncomputable section
namespace ContinuumCoulomb.QuantumEvenTapeGeometry
open QuantumRouteCode QuantumListSchedule MediatorGraph
open scoped Classical

variable {G : QMARationalExchangeGraph} (P : QMAPlanarRouteData G)
    {m : ℕ} (labels : G.Edge ≃ Fin m) (N : ℚ)

def input : QuantumEvenTapeProgram.Input :=
  (N,((G.n,QuantumListGraph.packed G labels,G.constant),
    List.ofFn P.position,List.ofFn (QuantumEvenRouteLabels.originalPath P labels)))

theorem input_valid : Valid (QuantumEvenTapeProgram.value (input P labels N)).1 :=
  QuantumEvenTapeProgram.value_valid _ (QuantumListGraph.packed_bounded G labels)

theorem count_eq : (QuantumEvenTapeProgram.value (input P labels N)).1.1=G.n+m*2 := by
  change G.n+(QuantumListGraph.packed G labels).length*2=G.n+m*2
  simp only [QuantumListGraph.packed,List.length_ofFn]

theorem bonds_length : (input P labels N).2.1.2.1.length=m := by
  exact List.length_ofFn

def tripleEquiv : Fin (QuantumEvenTapeProgram.entries (input P labels N)).length ≃
      Fin m × Fin 3 :=
  (QuantumEvenTapeProgram.tagEquiv (input P labels N)).trans
    (Equiv.prodCongr (finCongr (bonds_length P labels N)) (Equiv.refl _))

def vertex : Fin (QuantumEvenTapeProgram.value (input P labels N)).1.1 ≃
    Fin (P.toEven.schedule N).graph.n :=
  (finCongr (count_eq P labels N)).trans (QuantumEvenRouteLabels.vertex labels)

def edge : (schedule (QuantumEvenTapeProgram.value (input P labels N)).1
    (input_valid P labels N)).graph.Edge ≃ (P.toEven.schedule N).graph.Edge :=
  (tripleEquiv P labels N).trans (QuantumEvenRouteLabels.edgeEquiv labels)

theorem route_eq (i : Fin m) : QuantumEvenTapeProgram.route (input P labels N) i.val=
    QuantumEvenRouteLabels.originalPath P labels i := by
  unfold QuantumEvenTapeProgram.route input
  rw [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_ofFn]
  simp only [dite_eq_left i.isLt,Option.getD_some]

theorem source_eq (i : Fin m) :
    QuantumListSchedule.blockBondInput
      (QuantumEvenTapeProgram.blockInput (i.val,input P labels N))=
        (QuantumListPathStep.parameters (QuantumEvenTapeProgram.stepInput (input P labels N)),
          i.val,(G.left (labels.symm i)).val,(G.right (labels.symm i)).val,G.weight (labels.symm i)) := by
  unfold blockBondInput QuantumEvenTapeProgram.blockInput input QuantumListGraph.packed
  rw [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_ofFn]
  simp only [dite_eq_left i.isLt,Option.getD_some]

def tagLeft (t : Fin m × Fin 3) : Fin (G.n+m*2) :=
  ![fresh G.n m t.1 0,old G.n m (G.left (labels.symm t.1)),
    old G.n m (G.right (labels.symm t.1))] t.2
def tagRight (t : Fin m × Fin 3) : Fin (G.n+m*2) :=
  ![fresh G.n m t.1 1,fresh G.n m t.1 0,fresh G.n m t.1 0] t.2

private theorem fresh_val (i : Fin m) (a : Fin 2) :
    (fresh G.n m i a).val=G.n+2*i.val+a.val := by
  change G.n+(a.val+2*i.val)=_
  omega

private theorem old_val (v : Fin G.n) : (old G.n m v).val=v.val := rfl

theorem tag_left (t : Fin m × Fin 3) :
    QuantumEvenRouteLabels.vertex labels (tagLeft labels t)=
      (P.toEven.schedule N).graph.left (QuantumEvenRouteLabels.edge labels t) := by
  rcases t with ⟨i,k⟩
  fin_cases k
  · exact QuantumEvenRouteLabels.vertex_fresh labels i 0
  · change QuantumEvenRouteLabels.vertex labels (old G.n m (G.left (labels.symm i)))=
      old _ _ (G.left (QMAEvenRouteData.selected (QuantumEvenRouteLabels.activeIndex labels i)))
    rw [QuantumEvenRouteLabels.selected_index,QuantumEvenRouteLabels.vertex_old]
  · change QuantumEvenRouteLabels.vertex labels (old G.n m (G.right (labels.symm i)))=
      old _ _ (G.right (QMAEvenRouteData.selected (QuantumEvenRouteLabels.activeIndex labels i)))
    rw [QuantumEvenRouteLabels.selected_index,QuantumEvenRouteLabels.vertex_old]

theorem tag_right (t : Fin m × Fin 3) :
    QuantumEvenRouteLabels.vertex labels (tagRight (G := G) t)=
      (P.toEven.schedule N).graph.right (QuantumEvenRouteLabels.edge labels t) := by
  rcases t with ⟨i,k⟩
  fin_cases k
  · exact QuantumEvenRouteLabels.vertex_fresh labels i 1
  · exact QuantumEvenRouteLabels.vertex_fresh labels i 0
  · exact QuantumEvenRouteLabels.vertex_fresh labels i 0

theorem entry_tag (e : Fin (QuantumEvenTapeProgram.entries (input P labels N)).length) :
    (QuantumEvenTapeProgram.entries (input P labels N)).get e=
      (blockWork (QuantumEvenTapeProgram.blockInput
        ((tripleEquiv P labels N e).1.val,input P labels N)) (tripleEquiv P labels N e).2,
       QuantumListPathProgram.bond (blockBondInput (QuantumEvenTapeProgram.blockInput
        ((tripleEquiv P labels N e).1.val,input P labels N))) (tripleEquiv P labels N e).2) :=
  QuantumEvenTapeProgram.tagEquiv_get _ e

theorem literal_left (e : Fin (QuantumEvenTapeProgram.entries (input P labels N)).length) :
    finCongr (count_eq P labels N)
      ((schedule (QuantumEvenTapeProgram.value (input P labels N)).1
        (input_valid P labels N)).graph.left e)=tagLeft labels (tripleEquiv P labels N e) := by
  apply Fin.ext
  change ((QuantumEvenTapeProgram.entries (input P labels N)).get e).2.1=_
  rw [entry_tag]
  generalize tripleEquiv P labels N e=t
  rcases t with ⟨i,k⟩
  rw [source_eq]
  fin_cases k <;> simp [QuantumListPathProgram.bond,QuantumListPathProgram.left,tagLeft,
    QuantumListPathStep.parameters,QuantumEvenTapeProgram.stepInput,input,old_val,fresh_val]

theorem literal_right (e : Fin (QuantumEvenTapeProgram.entries (input P labels N)).length) :
    finCongr (count_eq P labels N)
      ((schedule (QuantumEvenTapeProgram.value (input P labels N)).1
        (input_valid P labels N)).graph.right e)=tagRight (G := G) (tripleEquiv P labels N e) := by
  apply Fin.ext
  change ((QuantumEvenTapeProgram.entries (input P labels N)).get e).2.2.1=_
  rw [entry_tag]
  generalize tripleEquiv P labels N e=t
  rcases t with ⟨i,k⟩
  rw [source_eq]
  fin_cases k <;> simp [QuantumListPathProgram.bond,QuantumListPathProgram.right,tagRight,
    QuantumListPathStep.parameters,QuantumEvenTapeProgram.stepInput,input,fresh_val]

theorem literal_work (e : Fin (QuantumEvenTapeProgram.entries (input P labels N)).length) :
    (schedule (QuantumEvenTapeProgram.value (input P labels N)).1
      (input_valid P labels N)).work e=
        QuantumEvenRouteLabels.work P labels (tripleEquiv P labels N e) := by
  change ((QuantumEvenTapeProgram.entries (input P labels N)).get e).1=_
  rw [entry_tag]
  generalize tripleEquiv P labels N e=t
  rcases t with ⟨i,k⟩
  change (if k=2 then 4*((QuantumEvenTapeProgram.route (input P labels N) i.val).length-1)-1
      else 0)=_
  rw [route_eq]
  simp only [QuantumEvenRouteLabels.originalPath,List.length_map,List.length_range,
    Nat.add_sub_cancel,QuantumEvenRouteLabels.work]

def relabel : QMAPathRelabeling
    (schedule (QuantumEvenTapeProgram.value (input P labels N)).1 (input_valid P labels N))
    (P.toEven.schedule N) where
  vertex := vertex P labels N
  edge := edge P labels N
  left e := (congrArg (QuantumEvenRouteLabels.vertex labels)
    (literal_left P labels N e)).trans (tag_left P labels N _)
  right e := (congrArg (QuantumEvenRouteLabels.vertex labels)
    (literal_right P labels N e)).trans (tag_right P labels N _)
  work e := (literal_work P labels N e).trans
    (QuantumEvenRouteLabels.work_eq P labels _).symm

def embedding : QMAPathEmbedding
    (schedule (QuantumEvenTapeProgram.value (input P labels N)).1 (input_valid P labels N)) :=
  (relabel P labels N).symm.transport (P.toEven.embedding N)

private theorem ofFn_cast {α : Type} {a b : ℕ} (h : a=b) (f : Fin b → α) :
    List.ofFn (fun i => f (finCongr h i))=List.ofFn f := by
  subst b
  rfl

theorem entry_count : (QuantumEvenTapeProgram.entries (input P labels N)).length=m*3 := by
  rw [QuantumEvenTapeProgram.entries_length,bonds_length]

theorem triple_cast (i : Fin (QuantumEvenTapeProgram.entries (input P labels N)).length) :
    tripleEquiv P labels N i=finProdFinEquiv.symm (finCongr (entry_count P labels N) i) := by
  apply Prod.ext <;> apply Fin.ext <;> rfl

theorem represents : QuantumListRouteProgram.Represents
    (QuantumEvenTapeProgram.value (input P labels N)) (input_valid P labels N)
      (embedding P labels N) := by
  constructor
  · change QuantumEvenTapeProgram.positions (input P labels N)=
      List.ofFn (fun i => P.toEven.nextPosition
        (QuantumEvenRouteLabels.vertex labels (finCongr (count_eq P labels N) i)))
    have hp : QuantumEvenTapeProgram.positions (input P labels N)=
        List.ofFn (fun i => P.toEven.nextPosition (QuantumEvenRouteLabels.vertex labels i)) := by
      simpa only [QuantumEvenTapeProgram.positions,input,List.map_ofFn,Function.comp_def] using
        QuantumEvenRouteLabels.positions_eq P labels
    exact hp.trans (ofFn_cast (count_eq P labels N)
      (fun i => P.toEven.nextPosition (QuantumEvenRouteLabels.vertex labels i))).symm
  · change QuantumEvenTapeProgram.paths (input P labels N)=
      List.ofFn (fun e : Fin (QuantumEvenTapeProgram.entries (input P labels N)).length =>
        (List.range (2*(schedule (QuantumEvenTapeProgram.value (input P labels N)).1
          (input_valid P labels N)).work e+2)).map
            (P.toEven.nextPoint (QuantumEvenRouteLabels.edge labels (tripleEquiv P labels N e))))
    simp_rw [literal_work,triple_cast]
    have hp : QuantumEvenTapeProgram.paths (input P labels N)=
        List.ofFn (fun k : Fin (m*3) =>
          (List.range (2*QuantumEvenRouteLabels.work P labels (finProdFinEquiv.symm k)+2)).map
            (P.toEven.nextPoint (QuantumEvenRouteLabels.edge labels (finProdFinEquiv.symm k)))) :=
      QuantumEvenRouteLabels.allPaths_eq P labels
    exact hp.trans (ofFn_cast (entry_count P labels N)
      (fun k : Fin (m*3) =>
        (List.range (2*QuantumEvenRouteLabels.work P labels (finProdFinEquiv.symm k)+2)).map
          (P.toEven.nextPoint (QuantumEvenRouteLabels.edge labels (finProdFinEquiv.symm k))))).symm

theorem work_le (hL : ∀ e, P.length e≤20) :
    ∀ e ∈ (QuantumEvenTapeProgram.value (input P labels N)).1.2.2, e.1≤80 := by
  intro e he
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp he
  let j : Fin (QuantumEvenTapeProgram.entries (input P labels N)).length := ⟨i.val,i.isLt⟩
  change (schedule (QuantumEvenTapeProgram.value (input P labels N)).1
    (input_valid P labels N)).work j≤80
  rw [literal_work P labels N j]
  unfold QuantumEvenRouteLabels.work
  split
  · have h := hL (labels.symm (tripleEquiv P labels N j).1)
    omega
  · omega

theorem embedding_bounded {X Y : ℕ} (hbox : P.Bounded X Y) :
    (embedding P labels N).Bounded (8*X) (8*Y) :=
  (relabel P labels N).symm.transport_bounded (P.toEven.embedding N)
    (P.toEven.embedding_bounded N (P.toEven_bounded hbox))

theorem realizes (hN : 0<N) (hL : ∀ e, P.length e≤20) {X Y : ℕ}
    (hbox : P.Bounded X Y) :
    ∃ (hs : Valid (QuantumListRouteProgram.iterate N QuantumFinalRoutingProgram.rounds
        (QuantumEvenTapeProgram.value (input P labels N))).1)
      (Q : QMAPathEmbedding (schedule (QuantumListRouteProgram.iterate N QuantumFinalRoutingProgram.rounds
        (QuantumEvenTapeProgram.value (input P labels N))).1 hs)),
      QuantumListRouteProgram.Represents (QuantumListRouteProgram.iterate N QuantumFinalRoutingProgram.rounds
        (QuantumEvenTapeProgram.value (input P labels N))) hs Q ∧
      Q.Bounded (8*X) (8*Y) ∧
      (∀ e, qmaSquareGrid.Adj (Q.position ((schedule _ hs).graph.left e))
        (Q.position ((schedule _ hs).graph.right e))) ∧
      (QuantumListRouteProgram.iterate N QuantumFinalRoutingProgram.rounds (QuantumEvenTapeProgram.value (input P labels N))).1.1+
        (QuantumListRouteProgram.iterate N QuantumFinalRoutingProgram.rounds (QuantumEvenTapeProgram.value (input P labels N))).1.2.2.length≤
          5^QuantumFinalRoutingProgram.rounds*((QuantumEvenTapeProgram.value (input P labels N)).1.1+
            (QuantumEvenTapeProgram.value (input P labels N)).1.2.2.length) ∧
      |QuantumListSchedule.energy
          (QuantumListRouteProgram.iterate N QuantumFinalRoutingProgram.rounds (QuantumEvenTapeProgram.value (input P labels N))).1-
        QuantumListSchedule.energy (QuantumEvenTapeProgram.value (input P labels N)).1|≤(QuantumFinalRoutingProgram.rounds:ℝ)/(N:ℝ) := by
  exact QuantumListRouteProgram.compile_realization hN _ (input_valid P labels N)
    (embedding P labels N) (represents P labels N)
    (by rw [QuantumFinalRoutingProgram.rounds_eq]; exact work_le P labels N hL)
    (embedding_bounded P labels N hbox)

end ContinuumCoulomb.QuantumEvenTapeGeometry

end

end OAI
