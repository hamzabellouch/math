import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantReferenceMeanMetadata
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantSourceBoundsBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantSourceBoundsPair

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantReferenceSourceBounds
open Construction HistoryOccurrenceVariables HistorySymbolicEncoding
open HistoryRepresentativeSourceSeparation HistorySignedXiTransport HistoryGiantReferenceMean
open HistoryPairPattern HistoryPairGiantCoordinates HistoryActiveCoordinates HistoryGiantSourceBounds

theorem selected_reference_sourceDomain {d : Decomposition} {Bs BD Bz : ℝ}
    {k : ℕ} {L : ℝ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E) (V : ℕ → ℕ) (l : ℕ)
    (x : SourceAssignment C.sources
      (Template.current (Template.initial (2*(Conclusion.bulkSize k L/2)) k) l))
    (s : ℤ)
    (c : HistoryChoices C.sources (Template.initial (2*(Conclusion.bulkSize k L/2)) k) V l)
    (P Q : ℤ)
    (hx : (assignmentPrior C.sources
      (Template.current (Template.initial (2*(Conclusion.bulkSize k L/2)) k) l)).mass x ≠ 0)
    (hc : choicesMass C.sources (Template.initial (2*(Conclusion.bulkSize k L/2)) k) V l c ≠ 0)
    (hP : 0 < P) (hQ : 0 < Q)
    (hPc : |Real.log (P : ℝ)-(C.giantCenter : ℝ)| ≤ 1)
    (hQc : |Real.log (Q : ℝ)-(C.giantCenter : ℝ)| ≤ 1) :
    let seed := Template.initial (2*(Conclusion.bulkSize k L/2)) k
    let a := sourceState C.sources (Template.current seed l) x s
    let h := decodeHistory C.sources seed V l (giantState a P Q) c
    SourceDomain (Conclusion.bulkSize k L/2) k (C.giantCenter : ℝ)
      (C.cells.center (Conclusion.bulkSize k L/2)) h (fun i => (integerSample h i : ℝ)) := by
  let seed := Template.initial (2*(Conclusion.bulkSize k L/2)) k
  let a := sourceState C.sources (Template.current seed l) x s
  let h := decodeHistory C.sources seed V l (giantState a P Q) c
  change SourceDomain _ _ _ _ h _
  have hroot : ∀ q ∈ h.root.small, sourceMass C.sources q ≠ 0 := by
    simpa only [h,decodeHistory_root,giantState,a,sourceState] using
      assignedSlots_source_mass_ne_zero C.sources (Template.current seed l) x hx
  apply sourceDomain_of_slot_masses C h
  · exact decoded_tree_source_labels C.sources seed V l (giantState a P Q) c
      (Template.assignedSlots_matches C.sources (Template.current seed l) x)
  · intro i
    exact hroot _ (List.get_mem _ i)
  · exact decoded_internalSlot_mass C.sources seed V l (giantState a P Q) c hc
  · intro b
    cases b
    · simpa [h,integerSample,decodeHistory_root,giantState,hP.le,hQ.le] using
        (Int.cast_pos.mpr hP : (0 : ℝ) < (P : ℝ))
    · simpa [h,integerSample,decodeHistory_root,giantState,hP.le,hQ.le] using
        (Int.cast_pos.mpr hQ : (0 : ℝ) < (Q : ℝ))
  · intro b
    cases b
    · simpa [h,integerSample,decodeHistory_root,giantState,hP.le,hQ.le] using hPc
    · simpa [h,integerSample,decodeHistory_root,giantState,hP.le,hQ.le] using hQc

theorem selected_reference_sourceBounds {d : Decomposition} {Bs BD Bz : ℝ}
    {k : ℕ} {L : ℝ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E) (V : ℕ → ℕ) (l : ℕ)
    (x y : SourceAssignment C.sources
      (Template.current (Template.initial (2*(Conclusion.bulkSize k L/2)) k) l))
    (s t : ℤ)
    (c e : HistoryChoices C.sources (Template.initial (2*(Conclusion.bulkSize k L/2)) k) V l)
    (P Q : ℤ)
    (hx : (assignmentPrior C.sources
      (Template.current (Template.initial (2*(Conclusion.bulkSize k L/2)) k) l)).mass x ≠ 0)
    (hy : (assignmentPrior C.sources
      (Template.current (Template.initial (2*(Conclusion.bulkSize k L/2)) k) l)).mass y ≠ 0)
    (hc : choicesMass C.sources (Template.initial (2*(Conclusion.bulkSize k L/2)) k) V l c ≠ 0)
    (he : choicesMass C.sources (Template.initial (2*(Conclusion.bulkSize k L/2)) k) V l e ≠ 0)
    (hP : 0 < P) (hQ : 0 < Q)
    (hPc : |Real.log (P : ℝ)-(C.giantCenter : ℝ)| ≤ 1)
    (hQc : |Real.log (Q : ℝ)-(C.giantCenter : ℝ)| ≤ 1) :
    let seed := Template.initial (2*(Conclusion.bulkSize k L/2)) k
    let h := decodeHistory C.sources seed V l
      (giantState (sourceState C.sources (Template.current seed l) x s) P Q) c
    let g := decodeHistory C.sources seed V l
      (giantState (sourceState C.sources (Template.current seed l) y t) P Q) e
    SourceBounds (Conclusion.bulkSize k L/2) k (C.giantCenter : ℝ)
      (C.cells.center (Conclusion.bulkSize k L/2)) h (leftMap h g) (giantCoordinates h g)
      (pairBackground h g) (fun _ => (C.giantCenter : ℝ)-1)
      (fun _ => (C.giantCenter : ℝ)+1) ∧
    SourceBounds (Conclusion.bulkSize k L/2) k (C.giantCenter : ℝ)
      (C.cells.center (Conclusion.bulkSize k L/2)) g (rightMap h g) (giantCoordinates h g)
      (pairBackground h g) (fun _ => (C.giantCenter : ℝ)-1)
      (fun _ => (C.giantCenter : ℝ)+1) := by
  have hh := selected_reference_sourceDomain C V l x s c P Q hx hc hP hQ hPc hQc
  have hg := selected_reference_sourceDomain C V l y t e P Q hy he hP hQ hPc hQc
  dsimp only
  exact ⟨left_giant_sourceBounds _ _ hh, right_giant_sourceBounds _ _ hh hg⟩

end Ostmann.Arithmetic.HistoryGiantReferenceSourceBounds

end

end OAI
