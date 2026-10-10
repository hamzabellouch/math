import OAI.NumberTheory.DukePrimeDegree.Geometry.RemainingIntrinsicProduct
import OAI.NumberTheory.DukePrimeDegree.Geometry.NextGroupCoordinates
import OAI.NumberTheory.DukePrimeDegree.Geometry.ExtremalRemainingEntries

namespace OAI

/-! # Splitting off the next root in the actual product coordinates -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
open scoped Classical
namespace DukePrimeDegree
open PrimeDegreePackets
namespace InitialRootStep
variable {n : ℕ}

def rootOptionIndex (q : InitialRootStep n) : Option q.NextRoot ≃ ↥q.remaining where
  toFun p := match p with
    | none => ⟨q.root,q.mem_remaining⟩
    | some p => ⟨p.val,(Finset.mem_erase.mp p.prop).2⟩
  invFun p := if h : p.val = q.root then none else some ⟨p.val,Finset.mem_erase.mpr ⟨h,p.prop⟩⟩
  left_inv p := by
    cases p with
    | none => simp
    | some p => simp [(Finset.mem_erase.mp p.prop).1]
  right_inv p := by
    dsimp
    split_ifs with h
    · exact Subtype.ext h.symm
    · rfl

def splitRootCoordinates (q : InitialRootStep n) :
    (↥q.remaining → ℝ) ≃ᵐ ((q.NextRoot → ℝ) × ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : ↥q.remaining => ℝ) q.rootOptionIndex).symm.trans
    (MeasurableEquiv.piOptionEquivProd (fun _ => ℝ))

lemma splitRootCoordinates_apply (q : InitialRootStep n) (x : ↥q.remaining → ℝ) :
    q.splitRootCoordinates x =
      ((fun p => x ⟨p.val,(Finset.mem_erase.mp p.prop).2⟩),x ⟨q.root,q.mem_remaining⟩) := rfl

lemma splitRootCoordinates_preserves (q : InitialRootStep n) (ν : ↥q.remaining → Measure ℝ)
    [∀ p, SigmaFinite (ν p)] :
    MeasurePreserving q.splitRootCoordinates (Measure.pi ν)
      ((Measure.pi fun p : q.NextRoot => ν ⟨p.val,(Finset.mem_erase.mp p.prop).2⟩).prod
        (ν ⟨q.root,q.mem_remaining⟩)) := by
  let e := q.rootOptionIndex
  let E := MeasurableEquiv.piCongrLeft (fun _ : ↥q.remaining => ℝ) e
  let F := MeasurableEquiv.piOptionEquivProd (fun _ : Option q.NextRoot => ℝ)
  have hE := (measurePreserving_piCongrLeft (α := fun _ : ↥q.remaining => ℝ) ν e).symm E
  have hF : MeasurePreserving F (Measure.pi fun p => ν (e p))
      ((Measure.pi fun p : q.NextRoot => ν ⟨p.val,(Finset.mem_erase.mp p.prop).2⟩).prod
        (ν ⟨q.root,q.mem_remaining⟩)) := by
    have hi : MeasurePreserving F.symm
        ((Measure.pi fun p : q.NextRoot => ν ⟨p.val,(Finset.mem_erase.mp p.prop).2⟩).prod
          (ν ⟨q.root,q.mem_remaining⟩))
        (Measure.pi fun p => ν (e p)) :=
      ⟨F.symm.measurable,Measure.pi_map_piOptionEquivProd (fun p => ν (e p))⟩
    exact hi.symm F.symm
  exact hF.comp hE

def remainingFactor (q : InitialRootStep n) :
    (positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ) ≃ₜ
      positiveRootGeneratedGroup q.remaining :=
  positiveRootRightFactorHomeomorph q.remaining q.remaining_positive q.remaining_closed
    q.distinct q.mem_remaining q.next_closed

lemma remainingFactor_val (q : InitialRootStep n)
    (z : positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ) :
    (q.remainingFactor z).val = z.1.val * Matrix.SpecialLinearGroup.transvection q.distinct z.2 := rfl

lemma remainingFactor_entry (q : InitialRootStep n)
    (z : positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ)
    (i j : Fin n) :
    (q.remainingFactor z).val.val i j =
      z.1.val.val i j + if i = q.root.1 ∧ j = q.root.2 then z.2 else 0 := by
  let w : positiveRootGeneratedGroup q.remaining :=
    ⟨z.1.val,positiveRootGeneratedGroup_mono (Finset.erase_subset _ _) z.1.prop⟩
  change (z.1.val.val * Matrix.transvection q.root.1 q.root.2 z.2) i j = _
  by_cases hj : j = q.root.2
  · subst j
    rw [Matrix.mul_transvection_apply_same,q.remaining_standard_column w]
    by_cases hi : i = q.root.1 <;> simp [hi]
  · rw [Matrix.mul_transvection_apply_of_ne (i := q.root.1) (j := q.root.2) i j hj]
    simp [hj]

lemma remainingFactor_coordinates (q : InitialRootStep n)
    {D : Finset (Fin n)} (c : EliminationChain q.processed D)
    (hfinal : c.finalEntries = allPositiveRoots n)
    (z : positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ) :
    q.splitRootCoordinates (c.remainingGroupCoordinates q.initial hfinal (q.remainingFactor z)) =
      (q.nextGroupCoordinates z.1,z.2) := by
  erw [q.splitRootCoordinates_apply]
  apply Prod.ext
  · funext p
    change c.remainingGroupCoordinates q.initial hfinal (q.remainingFactor z)
      ⟨p.val,(Finset.mem_erase.mp p.prop).2⟩ = q.nextGroupCoordinates z.1 p
    erw [c.remainingGroupCoordinates_apply,q.nextGroupCoordinates_apply,q.remainingFactor_entry]
    have hp : ¬ (p.val.1 = q.root.1 ∧ p.val.2 = q.root.2) := by
      intro he
      exact (Finset.mem_erase.mp p.prop).1 (Prod.ext he.1 he.2)
    simp [hp]
  · change c.remainingGroupCoordinates q.initial hfinal (q.remainingFactor z)
      ⟨q.root,q.mem_remaining⟩ = z.2
    erw [c.remainingGroupCoordinates_apply,q.remainingFactor_entry,q.next_selected_entry]
    simp

end InitialRootStep
end DukePrimeDegree

end

end OAI
