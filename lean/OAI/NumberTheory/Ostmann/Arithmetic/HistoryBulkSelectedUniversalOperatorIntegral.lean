import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSelectedUniversalOperatorActualDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSelectedUniversalOperator
open Construction Conclusion HistoryBulkReferenceFrequencyFamily HistorySelectedJointIntegralBounds Filter

theorem actualNestedIntegral_norm_eventually (d : Decomposition) (Bs BD Bz : ℝ) (k : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase  →  C.blockBase-2<(C.giantCenter:ℝ)  → 
      ∀(s : ℕ)(outside : List ℕ),(∀q∈outside,0 < q) → outside.length=2*s → 
      ∀(l : ℕ)(σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2))))
      (x y : InternalSourceDraws C.sources (Template.initial (2*(bulkSize k L/2)) k) l)
      (i : RootFrequencyIndex (frequencyBound Bs BD Bz k L) l)
      (r : SupportedReference C.sources (Template.initial (2*(bulkSize k L/2)) k)
        (frequencyBound Bs BD Bz k L) outside l x y i.1.val i.1.val i.2)
      (a : ActualReferenceData C σ i r)(mixed : Bool),
      ‖actualNestedIntegral C mixed s a‖ ≤
        64*2^(2^l*(2*(bulkSize k L/2)))*mainAmplitude Bs k L l := by
  filter_upwards [selected_integer_plain_integrals_eventually d Bs BD Bz k] with L hL
  intro E C hblock hcenter s outside houtside hout l σ x y i r a mixed
  have hi := hL E C hblock hcenter s outside houtside hout l σ a.assignment
    i.1.val i.1.val a.plus a.minus
    (assembleHistoryChoices C.sources _ _ l i.2.1 x)
    (assembleHistoryChoices C.sources _ _ l i.2.2 y)
    a.assignment_mass a.left_choice_mass a.right_choice_mass
    a.plus_pos a.minus_pos a.plus_cell a.minus_cell (actualReference_left_supported C a) (actualReference_right_supported C a)
  cases mixed
  · exact hi.1
  · exact hi.2

end Ostmann.Arithmetic.HistoryBulkSelectedUniversalOperator

end

end OAI
