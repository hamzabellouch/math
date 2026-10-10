import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSelectedUniversalOperator

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSelectedUniversalOperator
open Construction Conclusion HistoryBulkReferenceFrequencyFamily HistoryRepresentativeSourceSeparation Filter
open scoped BigOperators
variable {sources : SourceFamily} {seed : List SourceSlot} {V : ℕ → ℕ}
  {outside : List ℕ} {l : ℕ} {x y : InternalSourceDraws sources seed l}

def presentComplexValue (refs : RootReferenceFamily sources seed V outside l x y)
    (F : RootPresent refs → ℂ) (i : RootFrequencyIndex V l) : ℂ :=
  if hi : (refs i).isSome then F ⟨i,hi⟩ else 0

theorem sum_presentComplexValue (refs : RootReferenceFamily sources seed V outside l x y)
    (F : RootPresent refs → ℂ) :
    (∑i,presentComplexValue refs F i)=∑i : RootPresent refs,F i := by
  classical
  have he : (∑i ∈ Finset.univ.filter (fun i => (refs i).isSome), presentComplexValue refs F i) =
      ∑i : RootPresent refs, presentComplexValue refs F i.val := Finset.sum_subtype _ (by simp) _
  have hp : ∀i : RootPresent refs,presentComplexValue refs F i.val=F i := by
    intro i
    simp only [presentComplexValue,dite_eq_left i.property]
    exact congrArg F (Subtype.ext rfl)
  rw [←Finset.sum_congr rfl (fun i _ =>hp i),←he]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i _ hn
  have hi : ¬(refs i).isSome := by simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hn
  simp only [presentComplexValue,dite_eq_right hi]

theorem weighted_present_family_eventually {Bs BD Bz : ℝ}
    (hBs : 0 ≤ Bs) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz) {k : ℕ} (hk : 0 < k)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᶠ L : ℝ in atTop, ∀l≤k,∀K m : ℕ,0 < m→
      ∀ (sources : SourceFamily) (seed : List SourceSlot) (outside : List ℕ),
      ∀ (x y : InternalSourceDraws sources seed l),
      ∀ (refs : RootReferenceFamily sources seed (frequencyBound Bs BD Bz k L) outside l x y),
      ∀ (mixed : Bool) (d : Decomposition) (σ : Equiv.Perm (Fin (2^l)×Fin m))
      (hp : ∀q∈outside,q.Prime)
      (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q),
      (∀i : RootPresent refs,PairAdmissible (rootLeftHistory refs i) (rootRightHistory refs i) outside) →
      (∀q∈outside,3 ≤ q) → ∀(I : RootPresent refs→ℂ)(A : ℝ),0 ≤ A →
      (∀i,‖I i‖≤A) →
      ‖∑j,presentComplexValue refs (fun i=>I i*
        referenceRootAverage mixed d K m σ hp hV (rootSelected refs i)) j‖ ≤
        A*(((3:ℝ)^(2^l))^outside.length)*
          Real.exp (2*(2:ℝ)^l*initialGap Bs k L+ρ*(bulkSize k L:ℝ)) := by
  filter_upwards [root_reference_frequency_average_eventually hBs hBD hBz hk hρ] with L hL
  intro l hl K m hm sources seed outside x y refs mixed d σ hp hV had hthree I A hA hI
  have hsum := hL l hl K m hm sources seed outside x y refs
  have hs : (∑i : RootPresent refs,referenceFrequencyAverage mixed K m (rootSelected refs i))≤
      Real.exp (2*(2:ℝ)^l*initialGap Bs k L+ρ*(bulkSize k L:ℝ)) := by
    cases mixed
    · simpa only [referenceFrequencyAverage,Bool.false_eq_true,ite_false,
        sum_rootOptionValue_eq_present] using hsum.1
    · simpa only [referenceFrequencyAverage,ite_true,sum_rootOptionValue_eq_present] using hsum.2
  rw [sum_presentComplexValue]
  calc
    _ ≤ ∑i : RootPresent refs,‖I i*referenceRootAverage mixed d K m σ hp hV (rootSelected refs i)‖ := norm_sum_le _ _
    _ ≤ ∑i : RootPresent refs,A*((((3:ℝ)^(2^l))^outside.length)*
        referenceFrequencyAverage mixed K m (rootSelected refs i)) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      exact mul_le_mul (hI i)
        (referenceRootAverage_norm_le mixed d K m σ hp hV (rootSelected refs i) (had i) hm hthree)
        (norm_nonneg _) hA
    _ = A*(((3:ℝ)^(2^l))^outside.length)*
        ∑i : RootPresent refs,referenceFrequencyAverage mixed K m (rootSelected refs i) := by
      simp only [←mul_assoc,Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (mul_nonneg hA (by positivity))

end Ostmann.Arithmetic.HistoryBulkSelectedUniversalOperator

end

end OAI
