import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedLabelSubdivision

namespace OAI

/-! Ordered support-label arrays for the seven third-order terms.  The
same literal three-entry partition selects the real factor and the two
matching-parity factors. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedLabelData
open scoped Classical

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def thirdBlock (mediator : ℕ) (xs : List Letter) : Fin 7 → List Letter :=
  let p := partition xs
  ![[],[(mediator,3)],p.1,p.2,p.2++[(mediator,3)],
    p.1.take 1++[(mediator,axis (p.1.take 1))],
    p.1.drop 1++[(mediator,axis (p.1.take 1))]]

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
theorem pair_tag (index : ι → ℕ) (xs : List ι) (w : ι → Fin 4) :
    tag index (QuantumOrderedTriple.partition xs w).1
      (QuantumOrderedTriple.pairWord xs w)=(partition (tag index xs w)).1 := by
  rw [QuantumOrderedTriple.pairWord,tag_restrict index _ w _ (fun _ h => h)]
  exact (congrArg Prod.fst (partition_tag index xs w)).symm

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
theorem real_tag (index : ι → ℕ) (xs : List ι) (w : ι → Fin 4) :
    tag index (QuantumOrderedTriple.partition xs w).2
      (QuantumOrderedTriple.third xs w)=(partition (tag index xs w)).2 := by
  rw [QuantumOrderedTriple.third,tag_restrict index _ w _ (fun _ h => h)]
  exact (congrArg Prod.snd (partition_tag index xs w)).symm

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
theorem third_first_tag (index : ι → ℕ) (xs : List ι) (w : ι → Fin 4) :
    tag index ((QuantumOrderedTriple.partition xs w).1.take 1)
      (QuantumOrderedTriple.first xs w)=(partition (tag index xs w)).1.take 1 := by
  rw [QuantumOrderedTriple.first,first_tag]
  exact congrArg (List.take 1) (congrArg Prod.fst (partition_tag index xs w)).symm

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
theorem third_second_tag (index : ι → ℕ) (xs : List ι) (w : ι → Fin 4) :
    tag index ((QuantumOrderedTriple.partition xs w).1.drop 1)
      (QuantumOrderedTriple.second xs w)=(partition (tag index xs w)).1.drop 1 := by
  rw [QuantumOrderedTriple.second,second_tag]
  exact congrArg (List.drop 1) (congrArg Prod.fst (partition_tag index xs w)).symm

omit [Fintype κ] [DecidableEq κ] in
theorem third_axis (index : ι → ℕ) (xs : List ι) (w : ι → Fin 4)
    (hlen : xs.length ≤ 3) (hx : xs.Nodup) :
    axis ((partition (tag index xs w)).1.take 1) =
      (QuantumPolarizedSubdivision.axis
        (decide (Odd (qmaPauliYCount (QuantumOrderedTriple.first xs w))))).val := by
  have hp := (congrArg Prod.fst (partition_tag index xs w)).symm
  rw [← hp]
  exact first_axis index _ w (QuantumOrderedTriple.pair_nodup xs w hlen hx) 1

omit [Fintype κ] in
theorem thirdBlock_tag (index : ι → ℕ) (slot : κ → ℕ)
    (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 3) (hx : ∀ e, (xs e).Nodup) (p : κ × Fin 7) :
    tag (Sum.elim index slot) (QuantumOrderedThird.outputSites xs w p)
      (QuantumOrderedThird.outputWord xs w p) =
      thirdBlock (slot p.1) (tag index (xs p.1) (w p.1)) p.2 := by
  rcases p with ⟨e,k⟩
  fin_cases k
  · rfl
  · change tag (Sum.elim index slot) [Sum.inr e]
      (Sum.elim (fun _ : ι => 0) (qmaSinglePauliWord e 3)) = [(slot e,3)]
    simp only [tag,List.map_cons,List.map_nil,Sum.elim_inr,qmaSinglePauliWord,ite_true]
    rfl
  · change tag (Sum.elim index slot) ((QuantumOrderedTriple.partition (xs e) (w e)).1.map Sum.inl)
      (Sum.elim (QuantumOrderedTriple.pairWord (xs e) (w e)) (fun _ => 0)) = _
    rw [tag_lift,pair_tag]
    rfl
  · change tag (Sum.elim index slot) ((QuantumOrderedTriple.partition (xs e) (w e)).2.map Sum.inl)
      (Sum.elim (QuantumOrderedTriple.third (xs e) (w e)) (fun _ => 0)) = _
    rw [tag_lift,real_tag]
    rfl
  · change tag (Sum.elim index slot)
      (QuantumOrderedSubdivision.appendMediator (QuantumOrderedTriple.partition (xs e) (w e)).2 e)
      (Sum.elim (QuantumOrderedTriple.third (xs e) (w e)) (qmaSinglePauliWord e 3)) = _
    rw [tag_appendMediator,real_tag]
    rfl
  · change tag (Sum.elim index slot)
      (QuantumOrderedSubdivision.appendMediator ((QuantumOrderedTriple.partition (xs e) (w e)).1.take 1) e)
      (Sum.elim (QuantumOrderedTriple.first (xs e) (w e))
        (qmaSinglePauliWord e (QuantumPolarizedSubdivision.axis
          (QuantumOrderedThird.phase xs w e)))) = _
    rw [tag_appendMediator,third_first_tag]
    change _ = (partition (tag index (xs e) (w e))).1.take 1 ++
      [(slot e,axis ((partition (tag index (xs e) (w e))).1.take 1))]
    rw [third_axis index (xs e) (w e) (hlen e) (hx e)]
    rfl
  · change tag (Sum.elim index slot)
      (QuantumOrderedSubdivision.appendMediator ((QuantumOrderedTriple.partition (xs e) (w e)).1.drop 1) e)
      (Sum.elim (QuantumOrderedTriple.second (xs e) (w e))
        (qmaSinglePauliWord e (QuantumPolarizedSubdivision.axis
          (QuantumOrderedThird.phase xs w e)))) = _
    rw [tag_appendMediator,third_second_tag]
    change _ = (partition (tag index (xs e) (w e))).1.drop 1 ++
      [(slot e,axis ((partition (tag index (xs e) (w e))).1.take 1))]
    rw [third_axis index (xs e) (w e) (hlen e) (hx e)]
    rfl

end ContinuumCoulomb.QuantumOrderedLabelData

end

end OAI
