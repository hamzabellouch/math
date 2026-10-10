import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReferenceAmplitude
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReferenceSources
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReplacementBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationRepresentativePatternsBasic

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
local instance squareReferencePatternInternalDecidable (seed : List SourceSlot) (l : ℕ) :
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

def decodedSquareReference : DecodedSquareReference C
    (pairedInternalOrigin (Template.initial (2*(bulkSize depth L/2)) depth) l)
    (pairedHistoryType (Template.initial (2*(bulkSize depth L/2)) depth) l) p b.val
    (frequencyBound Bs BD Bz depth L) outside l := by
  let bn := natBlockDraw p b Subtype.val Subtype.val_injective
  have hv : ∀i, (slot r.left r.right (pairedInternalEquiv
      (Template.initial (2*(bulkSize depth L/2)) depth) r.left r.right
      (leftDraw r).labels (rightDraw r).labels i)).value=expand p bn i := hslots
  let ep := representativeBlockEquiv (Template.initial (2*(bulkSize depth L/2)) depth)
    r.left r.right (leftDraw r).labels (rightDraw r).labels p bn hv
  refine
    { leftDraw := leftDraw r
      rightDraw := rightDraw r
      leftMass := r.left_choices_mass
      rightMass := r.right_choices_mass
      sample := r.fixedB x
      sourceSamples := fixedB_sourceSamples r x hx
      representative := ep.symm
      prime_eq := ?_
      sample_representative := fixedB_representative r x
      admissible := had }
  intro q
  have he := representativeBlockEquiv_prime (Template.initial (2*(bulkSize depth L/2)) depth)
    r.left r.right (leftDraw r).labels (rightDraw r).labels p bn hv (ep.symm q)
  change prime r.left r.right (ep.symm q)=bn.val q
  change prime r.left r.right (ep.symm q)=bn.val (ep (ep.symm q)) at he
  simpa only [Equiv.apply_symm_apply] using he

def principalSquareReference (sw : ℕ) (hout : outside.length=2*sw)
    (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz depth L j<q)
    (σ : Equiv.Perm (Frame.Slots (depth:=depth) (L:=L) (l:=l))) (K : ℕ) :
    PrincipalSquareReference C outside l p b.val where
  square := decodedSquareReference r x hx p b hslots had
  principal := principalAmplitude r sw hout hV σ K x
  left_eq := rfl
  right_eq := rfl
  newBulk := newBulk x

@[simp] theorem decodedSquareReference_sample :
    (decodedSquareReference r x hx p b hslots had).sample=r.fixedB x := rfl

@[simp] theorem principalSquareReference_newBulk (sw hout hV σ K) :
    (principalSquareReference r x hx p b hslots had sw hout hV σ K).newBulk=newBulk x := rfl

end Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReference

end

end OAI
