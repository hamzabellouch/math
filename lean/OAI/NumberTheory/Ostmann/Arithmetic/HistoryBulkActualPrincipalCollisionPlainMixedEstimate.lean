import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyOuterBackgroundMass
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionBackground
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionNumerics
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionPlainBackground
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionPlainErrorProperty
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionPlainMixedData
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionPlainSupport
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualRootReferenceFamilyWitness

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns Filter
open HistoryPairSourceLaws HistoryBulkSourceDisintegration HistoryBulkActualPrincipalBlockFamily
open HistoryBulkPrincipalCollisionError HistoryBulkActualRootReferenceFamily
open HistoryGiantReferenceMean HistoryBulkFibreGiantApproximationReference
open HistoryBulkFibreGiantErrorAverage HistoryBulkFibreGiantApproximation HistoryBulkFibreOriginalReference
attribute [local instance] Classical.propDecidable selectedCollisionInternalDecidable

variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

private theorem mixedCollisionEstimateProof
    (d : Decomposition) (Bs BD Bz H : ℝ) {k : ℕ}
    (hBs : 0≤Bs) (hH : 0≤H) (hk : 2≤k) :
    ∀ᶠ scale : ℝ in atTop, plainMixedErrorProperty d Bs BD Bz H k scale :=
  @Filter.Eventually.mono ℝ
    (backgroundErrorProperty d Bs BD Bz H k)
    (plainMixedErrorProperty d Bs BD Bz H k) atTop
    (selected_background_collision_error_eventually d Bs BD Bz H (k:=k) hBs hH hk)
    (fun _ he E C hG hGu hcl hcu hb hd spectator hspec hactual ds hds l hl σ hV =>
      plainMixedCollisionPrincipal_error_le C spectator ds hactual hl σ hV
        (he E C hG hGu hcl hcu hb hd spectator hspec l false true hl
          (spectatorList spectator ds) (spectatorList_length_le spectator ds)
          (spectatorList_source_mass spectator ds hds)
          (plainMixedReferences C spectator ds hactual hl σ hV)
          (plainMixedMask C spectator ds hactual hl σ)
          (plainMixedMask_mem C spectator ds hactual hl σ)))

theorem selected_plainMixedCollisionPrincipal_error_eventually
    (d : Decomposition) (Bs BD Bz H : ℝ) {k : ℕ}
    (hBs : 0≤Bs) (hH : 0≤H) (hk : 2≤k) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase →
      C.blockBase+favorableBlockWidth L≤Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀spectator : PrimeSource,
      (∀p:spectator.Sample,Real.exp ((1/2000:ℝ)*L)≤Real.log (p:ℕ) ∧
        Real.log (p:ℕ)≤Real.exp ((1/1000:ℝ)*L)) →
      ∀hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator,
      ∀ds : Fin (2*(bulkSize k L/2))→spectator.Sample,
      (∀q,spectator.law.mass (ds q)≠0) →
      ∀(l : ℕ)(hl : l≤k)(σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2))))
        (hV : ∀q∈spectatorList spectator ds,∀j≤l,frequencyBound Bs BD Bz k L j<q),
      ‖plainCollisionPrincipal (l:=l) C spectator ds hactual hl σ true hV true-
        plainCollisionPrincipal (l:=l) C spectator ds hactual hl σ true hV false‖≤
          Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)) ∧
      ‖plainCollisionPrincipal (l:=l) C spectator ds hactual hl σ true hV true-
        plainCollisionPrincipal (l:=l) C spectator ds hactual hl σ true hV false‖≤
          Real.exp (-H*(bulkSize k L:ℝ)) :=
  mixedCollisionEstimateProof d Bs BD Bz H (k:=k) hBs hH hk

end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision

end

end OAI
