import OAI.NumberTheory.Jacobsthal.Estimates.LargeGapCountErrors

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.CompactSmallCountErrors
open FinitePathGeometry PrimeHistories PrimeBinMembership ReferenceAdmission StrongSourceFamilies
open ActualCountErrorEdges ActualCountErrorMass SourcePrimeProductData
open LogarithmicBinPartition ErdosInverseCounts
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail


theorem uniform_compact_small_count_errors (K d : ℝ) (hK : 3 ≤ K) (hd : 0 < d) :
    ∃ C B₀ w₀ : ℝ,0 < C ∧ 3 ≤ B₀ ∧ 1 < w₀ ∧ ∀ B w top : ℝ,B₀ ≤ B → w₀ ≤ w →
      w < top → Real.log B ≤ d*Real.log w → ∀ z : Node,
      z.side=.even → 199/100 ≤ z.ratio → z.ratio ≤ 23/10 → Consistent z → z.cutoff=B → z.closed=true → w^B=top →
      ∀ Y : ℕ,0 < Y → ∀ residue : ℕ → ℕ,∀ eps : ℝ,0 ≤ eps → ∀ F : Finset (List ℕ),
      F ⊆ referencePrefixes w (sourcePrimeSet w top) z.side z.gap →
      (∀ ps∈F,(terminal w z ps).gap ≤ K ∧
        |wordCountError Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) residue (SmallSieveFinite.smallEuler ⌊w⌋₊) ps| ≤ eps) →
      (B^2/((Y:ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊))*(∑ ps∈F,
        |(modulusCount Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) residue ps.prod:ℝ)-
          ((Y:ℝ)/(ps.prod:ℝ))*SmallSieveFinite.smallEuler ⌊w⌋₊|) ≤ C*eps := by
  obtain ⟨C,B₀,W,hC,hB₀,hW,hMass⟩ := uniform_source_family_mass K d hK hd
  refine ⟨C,B₀,max W 2,hC,hB₀,hW.trans_le (le_max_left _ _),?_⟩
  intro B w top hB hw₀ htop hcomp z hi h199 h23 hz hcut hclosed hpower Y hY residue eps heps F hF hGood
  have hw : 1 < w := hW.trans_le ((le_max_left _ _).trans hw₀)
  have hw2 : 2 ≤ w := (le_max_right _ _).trans hw₀
  have hV : 0 < SmallSieveFinite.smallEuler ⌊w⌋₊ :=
    (inv_pos.mpr (zero_lt_one.trans hw)).trans_le (SmallSieveFinite.smallEuler_floor_ge_inv w hw2)
  have hp : ∀ ps∈F,0 < ps.prod := fun ps hps => (reference_word_product_data hw htop z.side z.gap ps (hF hps)).1
  rw [finite_count_error_weight B Y _ residue _ hY hV F hp]
  have he : (∑ ps∈F,prefixWeight ps*|wordCountError Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) residue
      (SmallSieveFinite.smallEuler ⌊w⌋₊) ps|) ≤ (∑ ps∈F,prefixWeight ps)*eps := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro ps hps
    exact mul_le_mul_of_nonneg_left (hGood ps hps).2 (prefixWeight_nonneg ps)
  have hsum := hMass B w top hB ((le_max_left _ _).trans hw₀) htop hcomp z hi h199 h23 hz hcut hclosed hpower F hF
    (fun ps hps => (hGood ps hps).1)
  have hh := mul_le_mul_of_nonneg_left he (sq_nonneg B)
  have hc := mul_le_mul_of_nonneg_right hsum heps
  nlinarith
end NumberTheoryLean.CompactSmallCountErrors


end Erdos970

end OAI
