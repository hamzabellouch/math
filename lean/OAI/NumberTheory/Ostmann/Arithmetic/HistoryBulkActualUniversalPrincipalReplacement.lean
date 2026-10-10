import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipalFrame
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPatternIntegralReplacementBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkUniversalPatternAggregationFamily

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceLaws HistoryBulkSourceDisintegration HistoryBulkReferenceFrequencyFamily
open HistoryBulkUniversalPatternAggregation HistoryBulkSelectedUniversalOperator
open HistoryBulkFibreGiantApproximation HistoryBulkFibreIntegralReplacementFrame
open HistoryBulkGoodPatternPrincipalFrame HistoryPairRepresentatives HistoryPairKernelReplacement
open HistoryBulkSelectedUniversalSymbolicFamily
attribute [local instance] Classical.propDecidable
local instance universalPrincipalReplacementInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
    {C : InitialSourceChoice d Bs BD Bz k L E} {outside : List ℕ}
    {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}

def transportReference (f : Frame (l:=l) C outside)
    (a : SelectedNonbulkSample C l)
    (σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2))))
    (h g : History l) (eh : f.left=h) (eg : f.right=g)
    (e : Block p ≃ Representative h g) :
    HistoryBulkPatternIntegralReplacement.Reference C outside l p := by
  subst h
  subst g
  exact { frame := f
          nonbulk := a
          permutation := σ
          representative := e
          mask := 1
          mask_mem := ⟨zero_le_one,le_rfl⟩ }

@[simp] theorem transportReference_frame (f : Frame (l:=l) C outside)
    (a : SelectedNonbulkSample C l)
    (σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2))))
    (h g : History l) (eh : f.left=h) (eg : f.right=g)
    (e : Block p ≃ Representative h g) :
    (transportReference f a σ h g eh eg e).frame=f := by
  subst h; subst g; rfl

@[simp] theorem transportReference_permutation (f : Frame (l:=l) C outside)
    (a : SelectedNonbulkSample C l)
    (σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2))))
    (h g : History l) (eh : f.left=h) (eg : f.right=g)
    (e : Block p ≃ Representative h g) :
    (transportReference f a σ h g eh eg e).permutation=σ := by
  subst h; subst g; rfl

theorem transportReference_weight (f : Frame (l:=l) C outside)
    (a : SelectedNonbulkSample C l)
    (σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2))))
    (h g : History l) (eh : f.left=h) (eg : f.right=g)
    (e : Block p ≃ Representative h g)
    (hs : h.Supported (frequencyBound Bs BD Bz k L) outside)
    (gs : g.Supported (frequencyBound Bs BD Bz k L) outside)
    (b : Block p → CommonSample C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l))
    (mixed : Bool) :
    (transportReference f a σ h g eh eg e).weight b mixed =
      ((∏q : Block p,symbolicKernel mixed h g hs gs (e q) (b q).val : ℝ):ℂ) := by
  subst h
  subst g
  simp only [transportReference,HistoryBulkPatternIntegralReplacement.Reference.weight,one_mul]
  rfl

def replacementReference (family : SymbolicPatternFamily C outside l p)
    (hp : ∀q∈outside,q.Prime) (i : RootPresent family.refs) :
    HistoryBulkPatternIntegralReplacement.Reference C outside l p :=
  transportReference (frameOfData (family.data i) hp)
    (selectedSourceEquiv C l (family.data i).assignment).1 family.permutation
    (rootLeftHistory family.refs i) (rootRightHistory family.refs i)
    (frameOfData_left (family.data i) hp) (frameOfData_right (family.data i) hp)
    (family.representative i)

@[simp] theorem replacementReference_frame (family : SymbolicPatternFamily C outside l p)
    (hp : ∀q∈outside,q.Prime) (i : RootPresent family.refs) :
    (replacementReference family hp i).frame=frameOfData (family.data i) hp := by
  exact transportReference_frame _ _ _ _ _ _ _ _

@[simp] theorem replacementReference_permutation (family : SymbolicPatternFamily C outside l p)
    (hp : ∀q∈outside,q.Prime) (i : RootPresent family.refs) :
    (replacementReference family hp i).permutation=family.permutation := by
  exact transportReference_permutation _ _ _ _ _ _ _ _

theorem replacementReference_term
    (family : SymbolicPatternFamily C outside l p)
    (hp : ∀q∈outside,q.Prime) (i : RootPresent family.refs)
    (hσ : family.permutation=Equiv.refl _)
    (mixed : Bool) (hm : family.mask i=assignmentDensity (family.data i).assignment mixed)
    (b : Block p → CommonSample C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l))
    (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q) :
    (replacementReference family hp i).weight b mixed *
      (rootDensity (replacementReference family hp i).frame mixed *
        principalOperator (replacementReference family hp i).frame false mixed
          (replacementReference family hp i).permutation hV) =
      symbolicFamilyWeight family.refs b family.representative mixed family.mask i *
        actualNestedIntegral C mixed (bulkSize k L/2) (family.data i) *
          referenceRootAverage mixed d k (2*(bulkSize k L/2)) family.permutation hp hV
            (rootSelected family.refs i) := by
  rw [show (replacementReference family hp i).weight b mixed =
      ((∏q : Block p,symbolicKernel mixed (rootLeftHistory family.refs i)
        (rootRightHistory family.refs i) (rootLeftHistory_supported family.refs i)
        (rootRightHistory_supported family.refs i) (family.representative i q) (b q).val : ℝ):ℂ)
      from transportReference_weight _ _ _ _ _ _ _ _ _ _ _ _]
  rw [replacementReference_frame,replacementReference_permutation,←frameOfData_density]
  have ho := frameOfData_operator_of_identity (family.data i) hσ hp mixed hV
  rw [ho,symbolicFamilyWeight,hm,Complex.ofReal_mul]
  ring

end Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal

end

end OAI
