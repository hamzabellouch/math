import OAI.NumberTheory.Jacobsthal.Analysis.CompactSmallCountErrors

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.CountErrorRemainder
open FinitePathGeometry PrimeHistories PrimeBinMembership ReferenceAdmission
open CountErrorClassification LargeGapCountErrors CompactSmallCountErrors CountErrorFamilyMajorant
open LogarithmicBinPartition
open ErdosPrimeInputs.PrimePrefixMass

attribute [local instance] Classical.propDecidable

theorem uniform_count_error_remainder (aStar d eta : ℝ) (ha : 0 < aStar) (hd : 0 < d) (heta : 0 < eta) :
    ∃ Cbad K₀ : ℝ,0 < Cbad ∧ 3 ≤ K₀ ∧ ∀ K : ℝ,K₀ ≤ K →
      ∃ Csmall B₀ w₀ : ℝ,0 < Csmall ∧ 3 ≤ B₀ ∧ 1 < w₀ ∧
      ∀ B w top : ℝ,B₀ ≤ B → w₀ ≤ w → w < top → Real.log B ≤ d*Real.log w →
      ∀ Y : ℕ,0 < Y → ∀ z : Node,z.gap=Real.log (Y:ℝ)/Real.log w-aStar+2 →
      z.side=.even → 199/100 ≤ z.ratio → z.ratio ≤ 23/10 → Consistent z → z.cutoff=B → z.closed=true → w^B=top →
      ∀ residue : ℕ → ℕ,∀ eps : ℝ,0 ≤ eps → ∀ F : Finset (List ℕ),
      F ⊆ referencePrefixes w (sourcePrimeSet w top) z.side z.gap →
      let small := LargePrimeDeletion.cutoffPrimes ⌊w⌋₊
      let V0 := SmallSieveFinite.smallEuler ⌊w⌋₊
      (B^2/((Y:ℝ)*V0))*errorSum Y small residue V0 F ≤ eta+Csmall*eps+
        Cbad*(B^2*(∑ ps∈badCompactWords w K eps Y small residue V0 z F,prefixWeight ps)) := by
  obtain ⟨Cbad,WD,hCbad,hWD,hDiscard⟩ := count_error_family_majorant aStar ha
  obtain ⟨K₀,BG,WG,hK₀,hBG,hWG,hLarge⟩ := uniform_large_gap_count_errors aStar d eta ha hd heta
  refine ⟨Cbad,K₀,hCbad,hK₀,?_⟩
  intro K hK
  obtain ⟨Csmall,BC,WC,hCsmall,hBC,hWC,hCompact⟩ := uniform_compact_small_count_errors K d (hK₀.trans hK) hd
  refine ⟨Csmall,max BG BC,max WG (max WC WD),hCsmall,hBG.trans (le_max_left _ _),hWG.trans_le (le_max_left _ _),?_⟩
  intro B w top hB hw htop hcomp Y hY z hroot hi h199 h23 hz hcut hclosed hpower residue eps heps F hF
  dsimp only
  let small := LargePrimeDeletion.cutoffPrimes ⌊w⌋₊
  let V0 := SmallSieveFinite.smallEuler ⌊w⌋₊
  have hB3 : 3 ≤ B := hBG.trans ((le_max_left _ _).trans hB)
  have hA := hLarge K B w top hK ((le_max_left _ _).trans hB) ((le_max_left _ _).trans hw) htop hcomp
    Y hY z hroot hi h199 h23 hz hcut hclosed hpower residue (largeGapWords w K z F)
    (fun ps hp => hF (Finset.mem_filter.mp hp).1) (fun ps hp => (Finset.mem_filter.mp hp).2)
  have hBnd := hCompact B w top ((le_max_right _ _).trans hB) ((le_trans (le_max_left _ _) (le_max_right _ _)).trans hw)
    htop hcomp z hi h199 h23 hz hcut hclosed hpower Y hY residue eps heps
    (smallErrorWords w K eps Y small residue V0 z F)
    (fun ps hp => hF (Finset.mem_filter.mp hp).1) (fun ps hp => (Finset.mem_filter.mp hp).2)
  have hD := hDiscard B w top hB3 ((le_trans (le_max_right _ _) (le_max_right _ _)).trans hw) htop
    Y hY z hroot hi h199 hz hcut hclosed hpower residue (badCompactWords w K eps Y small residue V0 z F)
    (fun ps hp => hF (Finset.mem_filter.mp hp).1)
  have hPart := congrArg (fun t : ℝ => (B^2/((Y:ℝ)*V0))*t) (error_sum_partition w K eps Y small residue V0 z F)
  unfold errorSum at hPart ⊢
  change (B^2/((Y:ℝ)*V0))*(∑ ps∈F,|(ErdosInverseCounts.modulusCount Y small residue ps.prod:ℝ)-((Y:ℝ)/(ps.prod:ℝ))*V0|) ≤ _
  nlinarith
end NumberTheoryLean.CountErrorRemainder


end Erdos970

end OAI
