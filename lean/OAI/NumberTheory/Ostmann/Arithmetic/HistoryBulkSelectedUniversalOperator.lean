import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSelectedUniversalOperatorBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSelectedUniversalOperator
open Construction Conclusion HistoryBulkReferenceFrequencyFamily HistoryRepresentativeSourceSeparation Filter
open scoped BigOperators

variable {sources : SourceFamily} {seed : List SourceSlot} {V : ℕ → ℕ}
  {outside : List ℕ} {l : ℕ} {x y : InternalSourceDraws sources seed l}

theorem weighted_root_family_le
    (refs : RootReferenceFamily sources seed V outside l x y)
    (mixed : Bool) (d : Decomposition) (K m : ℕ)
    (σ : Equiv.Perm (Fin (2^l)×Fin m))
    (hp : ∀q∈outside,q.Prime) (hV : ∀q∈outside,∀j≤l,V j<q)
    (had : ∀i : RootPresent refs, PairAdmissible (rootLeftHistory refs i) (rootRightHistory refs i) outside)
    (hm : 0 < m) (hthree : ∀q∈outside,3 ≤ q)
    (I : ∀i : RootFrequencyIndex V l, SupportedReference sources seed V outside l x y i.1.val i.1.val i.2 → ℂ)
    (A : ℝ) (hA : 0 ≤ A) (hI : ∀i : RootPresent refs, ‖I i.val (rootSelected refs i)‖≤A) :
    ‖∑i,rootComplexValue refs (fun i r=>I i r*referenceRootAverage mixed d K m σ hp hV r) i‖ ≤
      A*(((3:ℝ)^(2^l))^outside.length)*
        ∑i,rootOptionValue refs (fun _ r=>referenceFrequencyAverage mixed K m r) i := by
  classical
  rw [sum_rootComplexValue_eq_present,sum_rootOptionValue_eq_present]
  calc
    _ ≤ ∑i : RootPresent refs, ‖I i.val (rootSelected refs i)*
        referenceRootAverage mixed d K m σ hp hV (rootSelected refs i)‖ := norm_sum_le _ _
    _ ≤ ∑i : RootPresent refs, A*((((3:ℝ)^(2^l))^outside.length)*
        referenceFrequencyAverage mixed K m (rootSelected refs i)) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      exact mul_le_mul (hI i)
        (referenceRootAverage_norm_le mixed d K m σ hp hV (rootSelected refs i) (had i) hm hthree)
        (norm_nonneg _) hA
    _ = _ := by simp only [←mul_assoc,Finset.mul_sum]

theorem weighted_root_family_eventually {Bs BD Bz : ℝ}
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
      (∀q∈outside,3 ≤ q) →
      ∀ (I : ∀i : RootFrequencyIndex (frequencyBound Bs BD Bz k L) l,
        SupportedReference sources seed (frequencyBound Bs BD Bz k L) outside l x y i.1.val i.1.val i.2 → ℂ),
      ∀A : ℝ,0 ≤ A → (∀i : RootPresent refs,‖I i.val (rootSelected refs i)‖≤A) →
      ‖∑i,rootComplexValue refs (fun i r=>I i r*referenceRootAverage mixed d K m σ hp hV r) i‖ ≤
        A*(((3:ℝ)^(2^l))^outside.length)*
          Real.exp (2*(2:ℝ)^l*initialGap Bs k L+ρ*(bulkSize k L:ℝ)) := by
  filter_upwards [root_reference_frequency_average_eventually hBs hBD hBz hk hρ] with L hL
  intro l hl K m hm sources seed outside x y refs mixed d σ hp hV had hthree I A hA hI
  have hsum := hL l hl K m hm sources seed outside x y refs
  have hsum' : (∑i,rootOptionValue refs (fun _ r=>referenceFrequencyAverage mixed K m r) i) ≤
      Real.exp (2*(2:ℝ)^l*initialGap Bs k L+ρ*(bulkSize k L:ℝ)) := by
    cases mixed
    · exact hsum.1
    · exact hsum.2
  exact (weighted_root_family_le refs mixed d K m σ hp hV had hm hthree I A hA hI).trans
    (mul_le_mul_of_nonneg_left hsum' (mul_nonneg hA (by positivity)))

end Ostmann.Arithmetic.HistoryBulkSelectedUniversalOperator

end

end OAI
