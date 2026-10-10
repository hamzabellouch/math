import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedLabelData

namespace OAI

/-! Literal bounded arrays for polarized subdivision.  The exact array
identity below keeps the supplied site order and the matching mediator. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedLabelData
open scoped Classical

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def subdivision (mediator d : ℕ) (xs : List Letter) : Fin 4 → List Letter :=
  ![[],[(mediator,3)],xs.take d++[(mediator,axis (xs.take d))],
    xs.drop d++[(mediator,axis (xs.take d))]]

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem tag_lift (index : ι → ℕ) (slot : κ → ℕ) (xs : List ι)
    (w : ι → Fin 4) (v : κ → Fin 4) :
    tag (Sum.elim index slot) (xs.map Sum.inl) (Sum.elim w v) =tag index xs w := by
  simp only [tag,List.map_map,Function.comp_def,Sum.elim_inl]

omit [Fintype ι] [Fintype κ] [DecidableEq ι] in
theorem tag_appendMediator (index : ι → ℕ) (slot : κ → ℕ) (xs : List ι)
    (w : ι → Fin 4) (e : κ) (a : Fin 4) :
    tag (Sum.elim index slot) (QuantumOrderedSubdivision.appendMediator xs e)
      (Sum.elim w (qmaSinglePauliWord e a)) =tag index xs w++[(slot e,a.val)] := by
  simp only [QuantumOrderedSubdivision.appendMediator,tag,List.map_append,List.map_map,
    Function.comp_def,Sum.elim_inl,List.map_cons,List.map_nil,Sum.elim_inr,
    qmaSinglePauliWord,ite_true]

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
theorem first_tag (index : ι → ℕ) (xs : List ι) (w : ι → Fin 4) (d : ℕ) :
    tag index (xs.take d) (QuantumOrderedSplit.firstWord xs d w) =
      (tag index xs w).take d := by
  rw [QuantumOrderedSplit.firstWord,QuantumOrderedSplit.left,
    tag_restrict index (xs.take d) w (xs.take d) (fun _ h => h),tag_take]

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
theorem second_tag (index : ι → ℕ) (xs : List ι) (w : ι → Fin 4) (d : ℕ) :
    tag index (xs.drop d) (QuantumOrderedSplit.secondWord xs d w) =
      (tag index xs w).drop d := by
  rw [QuantumOrderedSplit.secondWord,QuantumOrderedSplit.right,
    tag_restrict index (xs.drop d) w (xs.drop d) (fun _ h => h),tag_drop]

omit [Fintype κ] [DecidableEq κ] in
theorem first_axis (index : ι → ℕ) (xs : List ι) (w : ι → Fin 4)
    (hx : xs.Nodup) (d : ℕ) :
    axis ((tag index xs w).take d) =
      (QuantumPolarizedSubdivision.axis
        (decide (Odd (qmaPauliYCount (QuantumOrderedSplit.firstWord xs d w))))).val := by
  have hc := yCount_tag index (xs.take d) (QuantumOrderedSplit.firstWord xs d w)
    (hx.sublist (List.take_sublist d xs)) (qmaPauliRestrict_support _ _)
  rw [first_tag] at hc
  simp only [axis,hc,QuantumPolarizedSubdivision.axis,decide_eq_true_eq]
  split_ifs <;> rfl

omit [Fintype κ] in
theorem subdivision_tag (index : ι → ℕ) (slot : κ → ℕ)
    (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hx : ∀ e, (xs e).Nodup) (d : ℕ) (p : κ × Fin 4) :
    tag (Sum.elim index slot) (QuantumOrderedSubdivision.outputSites xs d p)
      (QuantumOrderedSubdivision.outputWord xs d w p) =
      subdivision (slot p.1) d (tag index (xs p.1) (w p.1)) p.2 := by
  rcases p with ⟨e,k⟩
  fin_cases k
  · rfl
  · change tag (Sum.elim index slot) [Sum.inr e]
      (Sum.elim (fun _ : ι => 0) (qmaSinglePauliWord e 3)) = [(slot e,3)]
    simp only [tag,List.map_cons,List.map_nil,Sum.elim_inr,qmaSinglePauliWord,ite_true]
    rfl
  · change tag (Sum.elim index slot) (QuantumOrderedSubdivision.appendMediator ((xs e).take d) e)
      (Sum.elim (QuantumOrderedSplit.firstWord (xs e) d (w e))
        (qmaSinglePauliWord e (QuantumPolarizedSubdivision.axis
          (QuantumOrderedSubdivision.phase xs d w e)))) =
        (tag index (xs e) (w e)).take d ++
          [(slot e,axis ((tag index (xs e) (w e)).take d))]
    rw [tag_appendMediator,first_tag,first_axis index (xs e) (w e) (hx e)]
    rfl
  · change tag (Sum.elim index slot) (QuantumOrderedSubdivision.appendMediator ((xs e).drop d) e)
      (Sum.elim (QuantumOrderedSplit.secondWord (xs e) d (w e))
        (qmaSinglePauliWord e (QuantumPolarizedSubdivision.axis
          (QuantumOrderedSubdivision.phase xs d w e)))) =
        (tag index (xs e) (w e)).drop d ++
          [(slot e,axis ((tag index (xs e) (w e)).take d))]
    rw [tag_appendMediator,second_tag,first_axis index (xs e) (w e) (hx e)]
    rfl

end ContinuumCoulomb.QuantumOrderedLabelData

end

end OAI
