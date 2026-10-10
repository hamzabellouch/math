import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagPrincipalMatchedFamily

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryBulkPrincipalCollisionError HistorySelectedPairDerivativeBounds Filter
attribute [local instance] Classical.propDecidable
local instance matchedPrincipalBoundInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _

theorem selected_matched_principal_family_weightBound_eventually (d : Decomposition)
    (Bs BD Bz : ℝ) {k : ℕ} (hBs : 0 ≤ Bs) (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase → C.blockBase-2 < (C.giantCenter:ℝ) →
      ∀(outside : List ℕ)(l : ℕ)(corrected mixed : Bool),
      (if corrected then l<k else l≤k) →
      ∀f g : FrequencyChoices (frequencyBound Bs BD Bz k L) l,
      ∀p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
      ∀F : MatchedPrincipalBlockFamily C outside l f g p,
      (F.toActive corrected mixed).WeightBound
        (selectedAmplitude (selectedExponent Bs BD Bz k+64) k L l outside) := by
  filter_upwards [selected_principalAmplitudeData_norm_eventually d Bs BD Bz hBs hk] with L hnorm
  intro E C hblock hcenter outside l corrected mixed hl f g p F y hy _hmass
  change F.weight corrected mixed y ≤ _
  apply (F.weight_le_principal_norm corrected mixed y hy).trans
  exact hnorm E C hblock hcenter outside l
    ((F.principal _ hy).amplitude (originalDrawBulk C l p y)) corrected mixed hl
    (originalDrawBulk C l p y)

end Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation

end

end OAI
