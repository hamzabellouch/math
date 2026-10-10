import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedLabelThird
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedPrivate

namespace OAI

/-! Exact sparse letters for YY removal and the final private-pair split.
Zero-labelled entries are retained so support-list order stays literal. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedLabelData
open scoped Classical

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def zeros (xs : List Letter) : List Letter := xs.map (fun p => (p.1,0))

def yyFactors (xs : List Letter) : List Letter × List Letter :=
  match xs with
  | [a,b] => if a.2=2 then
      ([(a.1,1),(b.1,3)],[(a.1,3),(b.1,1)]) else (xs,zeros xs)
  | _ => (xs,zeros xs)

def yyBlock (mediator : ℕ) (xs : List Letter) : Fin 4 → List Letter :=
  ![[],[(mediator,3)],(yyFactors xs).1++[(mediator,1)],
    (yyFactors xs).2++[(mediator,1)]]

def privateBlock (mediator : ℕ) (xs : List Letter) : Fin 4 → List Letter :=
  ![[],[(mediator,3)],xs.take 1++[(mediator,1)],xs.drop 1++[(mediator,1)]]

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem tag_zeros (index : ι → ℕ) (xs : List ι) (w : ι → Fin 4) :
    tag index xs (fun _ => 0)=zeros (tag index xs w) := by
  simp only [tag,zeros,List.map_map,Function.comp_def,Fin.val_zero]

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
theorem yyFactors_tag (index : ι → ℕ) (xs : List ι) (w : ι → Fin 4)
    (hx : xs.Nodup) :
    (tag index xs (QuantumOrderedYY.factor xs w).1,
      tag index xs (QuantumOrderedYY.factor xs w).2)=yyFactors (tag index xs w) := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    cases xs with
    | nil =>
      change (tag index [a] w,tag index [a] (fun _ => 0)) =
        (tag index [a] w,zeros (tag index [a] w))
      exact congrArg (fun z => (tag index [a] w,z)) (tag_zeros index [a] w)
    | cons b xs =>
      cases xs with
      | cons c xs =>
        change (tag index (a::b::c::xs) w,tag index (a::b::c::xs) (fun _ => 0)) =
          (tag index (a::b::c::xs) w,zeros (tag index (a::b::c::xs) w))
        exact congrArg (fun z => (tag index (a::b::c::xs) w,z))
          (tag_zeros index (a::b::c::xs) w)
      | nil =>
        have hab : a ≠ b := by simpa using hx
        have ha : (w a).val=2 ↔ w a=2 :=
          ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩
        by_cases h : w a=2
        · simp [QuantumOrderedYY.factor,yyFactors,tag,h,qmaTwoPauliWord,Ne.symm hab]
        · simp only [QuantumOrderedYY.factor,h,ite_false,tag,List.map_cons,List.map_nil,
            yyFactors,ha]
          exact Prod.ext rfl (tag_zeros index [a,b] w)

omit [Fintype ι] [Fintype κ] in
theorem yyBlock_tag (index : ι → ℕ) (slot : κ → ℕ)
    (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hx : ∀ e, (xs e).Nodup) (p : κ × Fin 4) :
    tag (Sum.elim index slot) (QuantumOrderedYY.outputSites xs p)
      (QuantumOrderedYY.outputWord xs w p) =
      yyBlock (slot p.1) (tag index (xs p.1) (w p.1)) p.2 := by
  rcases p with ⟨e,k⟩
  have hleft := congrArg Prod.fst (yyFactors_tag index (xs e) (w e) (hx e))
  have hright := congrArg Prod.snd (yyFactors_tag index (xs e) (w e) (hx e))
  dsimp only [Prod.fst,Prod.snd] at hleft hright
  fin_cases k
  · rfl
  · change tag (Sum.elim index slot) [Sum.inr e]
      (Sum.elim (fun _ : ι => 0) (qmaSinglePauliWord e 3)) = [(slot e,3)]
    simp only [tag,List.map_cons,List.map_nil,Sum.elim_inr,qmaSinglePauliWord,ite_true]
    rfl
  · change tag (Sum.elim index slot) (QuantumOrderedSubdivision.appendMediator (xs e) e)
      (Sum.elim (QuantumOrderedYY.factor (xs e) (w e)).1 (qmaSinglePauliWord e 1)) = _
    rw [tag_appendMediator,hleft]
    rfl
  · change tag (Sum.elim index slot) (QuantumOrderedSubdivision.appendMediator (xs e) e)
      (Sum.elim (QuantumOrderedYY.factor (xs e) (w e)).2 (qmaSinglePauliWord e 1)) = _
    rw [tag_appendMediator,hright]
    rfl

omit [Fintype ι] [Fintype κ] in
theorem privateBlock_tag (index : ι → ℕ) (slot : κ → ℕ)
    (xs : κ → List ι) (w : κ → ι → Fin 4) (p : κ × Fin 4) :
    tag (Sum.elim index slot) (QuantumOrderedPrivate.outputSites xs p)
      (QuantumOrderedPrivate.outputWord xs w p) =
      privateBlock (slot p.1) (tag index (xs p.1) (w p.1)) p.2 := by
  rcases p with ⟨e,k⟩
  fin_cases k
  · rfl
  · change tag (Sum.elim index slot) [Sum.inr e]
      (Sum.elim (fun _ : ι => 0) (qmaSinglePauliWord e 3)) = [(slot e,3)]
    simp only [tag,List.map_cons,List.map_nil,Sum.elim_inr,qmaSinglePauliWord,ite_true]
    rfl
  · change tag (Sum.elim index slot) (QuantumOrderedSubdivision.appendMediator ((xs e).take 1) e)
      (Sum.elim (QuantumOrderedSplit.firstWord (xs e) 1 (w e)) (qmaSinglePauliWord e 1)) = _
    rw [tag_appendMediator,first_tag]
    rfl
  · change tag (Sum.elim index slot) (QuantumOrderedSubdivision.appendMediator ((xs e).drop 1) e)
      (Sum.elim (QuantumOrderedSplit.secondWord (xs e) 1 (w e)) (qmaSinglePauliWord e 1)) = _
    rw [tag_appendMediator,second_tag]
    rfl

end ContinuumCoulomb.QuantumOrderedLabelData

end

end OAI
