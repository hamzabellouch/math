import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationRootPrincipals
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReferenceSplice
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReplacementDensityBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReference
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairPattern HistoryPairRows HistoryPairRepresentatives
open HistoryCompensationRepresentativePatterns HistoryPairVariableBSquareErrorSelected
open HistoryBulkFibreGiantApproximation HistoryPairSourceLaws HistorySymbolicEncoding
open HistoryRepresentativeSourceSeparation HistoryBulkPrincipalBSquareReplacement
open HistoryBulkReferencePeriodicMeanSource
attribute [local instance] Classical.propDecidable
local instance squareReferenceDensityInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {depth l : ℕ} {E : Finset ℕ}
variable {C : InitialSourceChoice d Bs BD Bz depth L E} {outside : List ℕ}
variable (r : Frame (l:=l) C outside) (x : Frame.Source (C:=C) (l:=l))
    (hx : (assignmentPrior C.sources _).mass x≠0)
variable (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize depth L/2)) depth) l))
    (b : BlockDraw p (CommonSample C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize depth L/2)) depth) l)))
    (hslots : ∀i, (slot r.left r.right (pairedInternalEquiv
      (Template.initial (2*(bulkSize depth L/2)) depth) r.left r.right
      (leftDraw r).labels (rightDraw r).labels i)).value=(expand p b i).val)
    (had : PairAdmissible r.left r.right outside)

variable (hout : outside.length=2*(bulkSize depth L/2))
    (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz depth L j<q)
    (σ : Equiv.Perm (Frame.Slots (depth:=depth) (L:=L) (l:=l)))

@[simp] theorem giantIntegralFactor_mixed (corrected : Bool) :
    giantIntegralFactor r corrected true x=r.mixedIntegralValue x corrected := rfl

theorem densityFactor_of_frame (X : DensitySources C l)
    (hX : X p b.val=r.leftSource) (mixed : Bool) :
    densityFactor X mixed p b.val=
      (if mixed then Frame.extractedDensity (C:=C) r.leftSource else 1) := by
  simp only [densityFactor,hX]

theorem density_principal_bMean_eq (corrected : Bool) :
    Frame.extractedDensity (C:=C) r.leftSource *
      ((principalSquareReference r x hx p b hslots had (bulkSize depth L/2) hout hV σ depth).principal.value
        corrected true
        (principalSquareReference r x hx p b hslots had (bulkSize depth L/2) hout hV σ depth).newBulk *
      HistoryBulkPrincipalBSquareReplacement.bMean
        (principalSquareReference r x hx p b hslots had (bulkSize depth L/2) hout hV σ depth) true)=
    r.mixedRootPrincipal hV σ x corrected := by
  rw [principalSquareReference_value_eq,principalSquareReference_bMean,
    giantIntegralFactor_mixed]
  simp only [ite_true,Frame.mixedRootPrincipal]
  ring

theorem density_principal_probabilityProduct_eq (corrected : Bool) :
    Frame.extractedDensity (C:=C) r.leftSource *
      ((principalSquareReference r x hx p b hslots had (bulkSize depth L/2) hout hV σ depth).principal.value
        corrected true
        (principalSquareReference r x hx p b hslots had (bulkSize depth L/2) hout hV σ depth).newBulk *
      HistoryBulkPrincipalBSquareReplacement.probabilityProduct
        (principalSquareReference r x hx p b hslots had (bulkSize depth L/2) hout hV σ depth) true)=
    Frame.extractedDensity (C:=C) r.leftSource *
      (r.mixedIntegralValue x corrected*r.rootValue true hV σ x*
        (probabilityProduct r true x:ℂ)) := by
  rw [principalSquareReference_value_eq,principalSquareReference_probabilityProduct,
    giantIntegralFactor_mixed]
  ring

theorem densityPatternFactor_eq_mixedRootPrincipal
    (R : ReferenceFamily C outside l) (X : DensitySources C l)
    (hR : R p b.val=some (principalSquareReference r x hx p b hslots had
      (bulkSize depth L/2) hout hV σ depth))
    (hX : X p b.val=r.leftSource)
    (probability corrected : Bool)
    (mask : ∀p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize depth L/2)) depth) l),
      (Block p → CommonSample C.sources
        (pairedInternalOrigin (Template.initial (2*(bulkSize depth L/2)) depth) l)) → Prop) :
    densityPatternFactor R X probability corrected true mask p b.val=
      (if mask p b.val then (1:ℂ) else 0)*
      (if probability then Frame.extractedDensity (C:=C) r.leftSource *
        (r.mixedIntegralValue x corrected*r.rootValue true hV σ x*
          (probabilityProduct r true x:ℂ))
       else r.mixedRootPrincipal hV σ x corrected) := by
  unfold densityPatternFactor principalPatternFactor principalValue optionalPrincipalBFactor
  rw [hR,densityFactor_of_frame r p b X hX]
  simp only [ite_true]
  cases probability with
  | false =>
    simp only [Bool.false_eq_true,ite_false]
    rw [←density_principal_bMean_eq r x hx p b hslots had hout hV σ corrected]
    ring
  | true =>
    simp only [ite_true]
    rw [←density_principal_probabilityProduct_eq r x hx p b hslots had hout hV σ corrected]
    ring

theorem densityPatternFactor_static_eq_mixedRootPrincipal
    (R : ReferenceFamily C outside l) (X : DensitySources C l)
    (hR : R p b.val=some (principalSquareReference r x hx p b hslots had
      (bulkSize depth L/2) hout hV σ depth))
    (hX : X p b.val=r.leftSource) (corrected : Bool)
    (y : Frame.Source (C:=C) (l:=l)) :
    densityPatternFactor R X false corrected true
      (fun _ _=>((r.newLeft x).root.small.map SmallSlot.value++outside).Pairwise Nat.Coprime ∧
        ((r.newRight y).root.small.map SmallSlot.value++outside).Pairwise Nat.Coprime) p b.val=
      staticPairMask (r.newLeft x) (r.newRight y) outside *
        r.mixedRootPrincipal hV σ x corrected := by
  rw [densityPatternFactor_eq_mixedRootPrincipal r x hx p b hslots had hout hV σ R X hR hX]
  rfl

end Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReference

end

end OAI
