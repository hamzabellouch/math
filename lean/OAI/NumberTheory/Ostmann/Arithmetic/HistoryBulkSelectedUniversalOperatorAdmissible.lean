import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSelectedUniversalOperatorActual
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryRepresentativeIntegerAdmissible

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSelectedUniversalOperator
open Construction Conclusion HistoryBulkReferenceFrequencyFamily
open HistoryRepresentativeSourceSeparation HistoryBulkGiantIntegerReference Filter

theorem actualReference_pair_admissible_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase → C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀spectator : PrimeSource,
      (∀p : spectator.Sample,Real.exp ((1/2000:ℝ)*L)≤Real.log (p:ℕ) ∧
        Real.log (p:ℕ)≤Real.exp ((1/1000:ℝ)*L)) →
      ∀outside : List ℕ,(∀p∈outside,p∈spectator.candidates) → ∀l,l≤k →
      ∀(σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2))))
      (x y : InternalSourceDraws C.sources (Template.initial (2*(bulkSize k L/2)) k) l)
      (i : RootFrequencyIndex (frequencyBound Bs BD Bz k L) l)
      (r : SupportedReference C.sources (Template.initial (2*(bulkSize k L/2)) k)
        (frequencyBound Bs BD Bz k L) outside l x y i.1.val i.1.val i.2)
      (_a : ActualReferenceData C σ i r),
      PairAdmissible
        (decodeHistory C.sources (Template.initial (2*(bulkSize k L/2)) k)
          (frequencyBound Bs BD Bz k L) l r.left (assembleHistoryChoices C.sources _ _ l i.2.1 x))
        (decodeHistory C.sources (Template.initial (2*(bulkSize k L/2)) k)
          (frequencyBound Bs BD Bz k L) l r.right (assembleHistoryChoices C.sources _ _ l i.2.2 y)) outside := by
  filter_upwards [HistoryRepresentativeIntegerAdmissible.selected_integer_pair_admissible_eventually
    d Bs BD Bz hk] with L hL
  intro E C hG hc hcu hb hd spectator hspec outside hout l hl σ x y i r a
  have hy : (assignmentPrior C.sources _).mass (permutedAssignment C l σ a.assignment)≠0 := by
    rw [permutedAssignment_mass]
    exact a.assignment_mass
  have hh := hL E C hG hc hcu hb hd spectator hspec outside hout l hl
    a.assignment (permutedAssignment C l σ a.assignment) i.1.val i.1.val a.plus a.minus
    (assembleHistoryChoices C.sources _ _ l i.2.1 x)
    (assembleHistoryChoices C.sources _ _ l i.2.2 y)
    a.assignment_mass hy a.left_choice_mass a.right_choice_mass
    (actualReference_left_supported C a) (actualReference_right_supported C a)
  simpa only [←a.left_eq,←a.right_eq] using hh

end Ostmann.Arithmetic.HistoryBulkSelectedUniversalOperator

end

end OAI
