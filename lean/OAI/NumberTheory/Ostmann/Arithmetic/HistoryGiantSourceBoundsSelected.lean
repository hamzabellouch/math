import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantSourceBoundsBasic
import OAI.NumberTheory.Ostmann.Construction.ActualAmplitude

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantSourceBounds
open Construction HistoryOccurrenceVariables HistorySymbolicEncoding
open HistoryRepresentativeSourceSeparation

theorem selected_decoded_sourceDomain {d : Decomposition} {Bs BD Bz : ℝ}
    {k : ℕ} {L : ℝ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E) (V : ℕ → ℕ) (l : ℕ)
    (x : OuterSample C.sources
      (Template.current (Template.initial (2*(Conclusion.bulkSize k L/2)) k) l) C.giant)
    (s : ℤ)
    (c : HistoryChoices C.sources (Template.initial (2*(Conclusion.bulkSize k L/2)) k) V l)
    (hx : (outerPrior C.sources
      (Template.current (Template.initial (2*(Conclusion.bulkSize k L/2)) k) l) C.giant).mass x ≠ 0)
    (hc : choicesMass C.sources (Template.initial (2*(Conclusion.bulkSize k L/2)) k) V l c ≠ 0) :
    let h := decodeHistory C.sources (Template.initial (2*(Conclusion.bulkSize k L/2)) k) V l
      (outerState C.sources
        (Template.current (Template.initial (2*(Conclusion.bulkSize k L/2)) k) l) C.giant x s) c
    SourceDomain (Conclusion.bulkSize k L/2) k (C.giantCenter : ℝ)
      (C.cells.center (Conclusion.bulkSize k L/2)) h (fun i => (integerSample h i : ℝ)) := by
  let seed := Template.initial (2*(Conclusion.bulkSize k L/2)) k
  let a := outerState C.sources (Template.current seed l) C.giant x s
  let h := decodeHistory C.sources seed V l a c
  change SourceDomain _ _ _ _ h _
  have hx' : C.giant.law.mass x.1 * (C.giant.law.mass x.2.1 *
      (assignmentPrior C.sources (Template.current seed l)).mass x.2.2) ≠ 0 := hx
  have hp := (mul_ne_zero_iff.mp hx').1
  have hm := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hx').2).1
  have ha := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hx').2).2
  have hroot : ∀ q ∈ h.root.small, sourceMass C.sources q ≠ 0 := by
    simpa only [h, decodeHistory_root, a, outerState] using
      assignedSlots_source_mass_ne_zero C.sources (Template.current seed l) x.2.2 ha
  apply sourceDomain_of_slot_masses C h
  · exact decoded_tree_source_labels C.sources seed V l a c
      (Template.assignedSlots_matches C.sources (Template.current seed l) x.2.2)
  · intro i
    exact hroot _ (List.get_mem _ i)
  · exact decoded_internalSlot_mass C.sources seed V l a c hc
  · intro b
    cases b
    · simpa only [h, integerSample, decodeHistory_root, a, outerState, Int.cast_natCast] using
        (Nat.cast_pos.mpr (C.giant.prime _ x.1.property).pos : 0 < (x.1.val : ℝ))
    · simpa only [h, integerSample, decodeHistory_root, a, outerState, Int.cast_natCast] using
        (Nat.cast_pos.mpr (C.giant.prime _ x.2.1.property).pos : 0 < (x.2.1.val : ℝ))
  · intro b
    cases b
    · simpa only [h, integerSample, decodeHistory_root, a, outerState, Int.cast_natCast] using
        (C.giant_log_support x.1 hp).le
    · simpa only [h, integerSample, decodeHistory_root, a, outerState, Int.cast_natCast] using
        (C.giant_log_support x.2.1 hm).le

end Ostmann.Arithmetic.HistoryGiantSourceBounds

end

end OAI
