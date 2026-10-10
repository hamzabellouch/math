import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationRootTestMixed
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReferenceDensity

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindex
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryBulkFibreGiantApproximation HistoryBulkPrincipalBSquareReference
open HistoryBulkPrincipalBSquareReplacement HistoryCompensationRepresentativePatterns
open HistoryPairRows HistoryRepresentativeSourceSeparation CanonicalHistoryLeafBulk
open HistoryBulkReferencePeriodicMeanSource
attribute [local instance] Classical.propDecidable
local instance sourceSquareInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  {C : InitialSourceChoice d Bs BD Bz k L E} {outside : List ℕ}
  (r : Frame (l:=l) C outside) (x : Frame.Source (C:=C) (l:=l))
  (hx : (assignmentPrior C.sources _).mass x≠0)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (b : BlockDraw p (CommonSample C.sources
    (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)))
  (hslots : ∀i,(slot r.left r.right (pairedInternalEquiv
    (Template.initial (2*(bulkSize k L/2)) k) r.left r.right
    (leftDraw r).labels (rightDraw r).labels i)).value=(expand p b i).val)
  (had : PairAdmissible r.left r.right outside)
  (hout : outside.length=2*(bulkSize k L/2))
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)
  (σ : Equiv.Perm (Frame.Slots (depth:=k) (L:=L) (l:=l)))

def squareBFactor (corrected mixed : Bool) : ℂ :=
  let R := principalSquareReference r x hx p b hslots had (bulkSize k L/2) hout hV σ k
  (if mixed then Frame.extractedDensity (C:=C) r.leftSource else 1) *
    (R.principal.value corrected mixed R.newBulk * bMean R mixed)

theorem squareBFactor_prime :
    squareBFactor r x hx p b hslots had hout hV σ false false =
      r.primeRootPrincipal hV σ x := by
  dsimp only [squareBFactor]
  rw [principalSquareReference_value_eq,principalSquareReference_bMean]
  simp only [Bool.false_eq_true,ite_false,one_mul,giantIntegralFactor_plain_prime,
    Frame.primeRootPrincipal]
  ring

theorem squareBFactor_mixed (corrected : Bool) :
    squareBFactor r x hx p b hslots had hout hV σ corrected true =
      r.mixedRootPrincipal hV σ x corrected := by
  exact density_principal_bMean_eq r x hx p b hslots had hout hV σ corrected

variable (y : Frame.Source (C:=C) (l:=l))
  (hfreq : ∀j≤l,∀origin,(C.sources origin).AboveFrequency (frequencyBound Bs BD Bz k L j))
  (hbulk : ∀u : Frame.Slots (depth:=k) (L:=L) (l:=l),
    bulkSamples C.sources (2*(bulkSize k L/2)) k l y u.1 u.2=
      bulkSamples C.sources (2*(bulkSize k L/2)) k l x (σ u).1 (σ u).2)
  (hfixed : ∀i:Fin (Template.current (Template.initial (2*(bulkSize k L/2)) k) l).length,
    ((Template.current (Template.initial (2*(bulkSize k L/2)) k) l).get i).role≠.bulk →
    (x i).val=(r.leftSource i).val)
  (hfixed' : ∀i:Fin (Template.current (Template.initial (2*(bulkSize k L/2)) k) l).length,
    ((Template.current (Template.initial (2*(bulkSize k L/2)) k) l).get i).role≠.bulk →
    (y i).val=(r.rightSource i).val)

include hfreq hbulk hfixed hfixed'

theorem masked_prime_eq_squareBFactor :
    staticPairMask (r.newLeft x) (r.newRight y) outside*r.principal σ x y =
      staticPairMask (r.newLeft x) (r.newRight y) outside*
        squareBFactor r x hx p b hslots had hout hV σ false false := by
  rw [squareBFactor_prime]
  exact r.masked_principal_eq_rootValue hV σ x y hx hfreq hbulk hfixed hfixed'

theorem masked_mixed_eq_squareBFactor (corrected : Bool) :
    staticPairMask (r.newLeft x) (r.newRight y) outside*
        (if corrected then r.principalCorrectedMixed σ x y else r.principalMixed σ x y) =
      staticPairMask (r.newLeft x) (r.newRight y) outside*
        squareBFactor r x hx p b hslots had hout hV σ corrected true := by
  rw [squareBFactor_mixed]
  exact r.masked_mixed_principal_from_block hV σ x y
    (r.masked_mixedBlockAverage_eq_rootValue hV σ x y hx hfreq hbulk hfixed hfixed')
    hfixed corrected

end Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindex

end

end OAI
