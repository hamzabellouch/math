import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceFrequencyFamilyRoots
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSelectedIntegralReplacementMeans

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSelectedUniversalOperator
open Construction HistoryBulkReferenceFrequencyFamily HistoryPairedFrequencyAverage
open HistoryBulkSelectedIntegralReplacement HistoryRepresentativeSourceSeparation
open HistoryBulkReplacementGeometry HistoryFrequencyResidues ResidueHaar HistoryBulkResidueNormSum
open scoped BigOperators

variable {sources : SourceFamily} {seed : List SourceSlot} {V : ℕ → ℕ}
  {outside : List ℕ} {l : ℕ} {x y : InternalSourceDraws sources seed l}

def rootComplexValue (refs : RootReferenceFamily sources seed V outside l x y)
    (F : ∀i : RootFrequencyIndex V l, SupportedReference sources seed V outside l x y i.1.val i.1.val i.2 → ℂ)
    (i : RootFrequencyIndex V l) : ℂ := (refs i).elim 0 (F i)

theorem rootComplexValue_present (refs : RootReferenceFamily sources seed V outside l x y)
    (F : ∀i : RootFrequencyIndex V l, SupportedReference sources seed V outside l x y i.1.val i.1.val i.2 → ℂ)
    (i : RootPresent refs) : rootComplexValue refs F i.val = F i.val (rootSelected refs i) := by
  rcases i with ⟨fg,hfg⟩
  cases he : refs fg with
  | none => simp only [he,Option.isSome_none,Bool.false_eq_true] at hfg
  | some r => simp only [rootComplexValue,rootSelected,he,Option.elim_some,Option.get_some]

theorem sum_rootComplexValue_eq_present (refs : RootReferenceFamily sources seed V outside l x y)
    (F : ∀i : RootFrequencyIndex V l, SupportedReference sources seed V outside l x y i.1.val i.1.val i.2 → ℂ) :
    (∑i, rootComplexValue refs F i) = ∑i : RootPresent refs, F i.val (rootSelected refs i) := by
  classical
  have he : (∑i ∈ Finset.univ.filter (fun i => (refs i).isSome), rootComplexValue refs F i) =
      ∑i : RootPresent refs, rootComplexValue refs F i.val :=
    Finset.sum_subtype _ (by simp) _
  rw [←Finset.sum_congr rfl (fun i _ => rootComplexValue_present refs F i), ←he]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i _ hn
  have hfalse : ¬(refs i).isSome := by simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hn
  cases heq : refs i with
  | none => simp only [rootComplexValue,heq,Option.elim_none]
  | some r => simp only [heq,Option.isSome_some,not_true_eq_false] at hfalse

variable {s t : ℤ} {fg : FrequencyChoices V l × FrequencyChoices V l}

def referenceRootAverage (mixed : Bool) (d : Decomposition) (K m : ℕ)
    (σ : Equiv.Perm (Fin (2^l)×Fin m))
    (hp : ∀q∈outside,q.Prime) (hV : ∀q∈outside,∀j≤l,V j<q)
    (r : SupportedReference sources seed V outside l x y s t fg) : ℂ :=
  let h := decodeHistory sources seed V l r.left (assembleHistoryChoices sources seed V l fg.1 x)
  let g := decodeHistory sources seed V l r.right (assembleHistoryChoices sources seed V l fg.2 y)
  letI : NeZero (bulkModulus h g outside K) :=
    ⟨actual_bulk_modulus_ne_zero h g r.left_supported r.right_supported hp K⟩
  average (rootTest false mixed d h g r.left_supported r.right_supported hp hV σ K)

def referenceFrequencyAverage (mixed : Bool) (K m : ℕ)
    (r : SupportedReference sources seed V outside l x y s t fg) : ℝ :=
  if mixed then referenceRingUnitAverage K m r else referenceUnitAverage K m r

theorem referenceRootAverage_norm_le (mixed : Bool) (d : Decomposition) (K m : ℕ)
    (σ : Equiv.Perm (Fin (2^l)×Fin m))
    (hp : ∀q∈outside,q.Prime) (hV : ∀q∈outside,∀j≤l,V j<q)
    (r : SupportedReference sources seed V outside l x y s t fg)
    (had : PairAdmissible
      (decodeHistory sources seed V l r.left (assembleHistoryChoices sources seed V l fg.1 x))
      (decodeHistory sources seed V l r.right (assembleHistoryChoices sources seed V l fg.2 y)) outside)
    (hm : 0 < m) (hthree : ∀q∈outside,3 ≤ q) :
    ‖referenceRootAverage mixed d K m σ hp hV r‖ ≤
      (((3:ℝ)^(2^l))^outside.length)*referenceFrequencyAverage mixed K m r := by
  cases mixed
  · exact rootTest_canonical_unit_average_le d _ _ r.left_supported r.right_supported hp hV σ K had hm hthree
  · exact rootTest_canonical_mixed_average_le d _ _ r.left_supported r.right_supported hp hV σ K had hm hthree

end Ostmann.Arithmetic.HistoryBulkSelectedUniversalOperator

end

end OAI
