import OAI.NumberTheory.Jacobsthal.Estimates.CountErrorRemainder

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.StoppedErrorReduction
open FinitePathGeometry PrimeHistories PrimeBinMembership ReferenceAdmission
open CountErrorRemainder CountErrorClassification LiteralCountErrorLedger
open StoppedCountVertex StoppedCountAdapters StoppedVertexHistory StoppedTraceSets
open LogarithmicBinPartition
open ErdosPrimeInputs.PrimePrefixMass

attribute [local instance] Classical.propDecidable

theorem stopped_error_reduction (aStar d eta : ℝ) (ha : 0 < aStar) (hd : 0 < d) (heta : 0 < eta) :
    ∃ Cbad K₀ : ℝ,0 < Cbad ∧ 3 ≤ K₀ ∧ ∀ K : ℝ,K₀ ≤ K →
      ∃ Csmall B₀ w₀ : ℝ,0 < Csmall ∧ 3 ≤ B₀ ∧ 1 < w₀ ∧
      ∀ B w top : ℝ,B₀ ≤ B → w₀ ≤ w → w < top → Real.log B ≤ d*Real.log w →
      ∀ Y : ℕ,0 < Y → ∀ z : Node,z.gap=Real.log (Y:ℝ)/Real.log w-aStar+2 →
      z.side=.even → 199/100 ≤ z.ratio → z.ratio ≤ 23/10 → Consistent z → z.cutoff=B → z.closed=true → w^B=top →
      ∀ residue : ℕ → ℕ,∀ eps : ℝ,0 ≤ eps → ∀ stop : List ℕ → Prop,
      let P := sourcePrimeSet w top
      let small := LargePrimeDeletion.cutoffPrimes ⌊w⌋₊
      let V0 := SmallSieveFinite.smallEuler ⌊w⌋₊
      let v := rootVertex z ∅ P ((Y:ℝ)*V0)
      B^2*referencePolynomial w P z.side z.gap+
        (B^2/((Y:ℝ)*V0))*(∑ ps∈stopped w stop P.card v,
          (countSurvivors Y small residue (after w v ps)-referenceValue w (after w v ps))) -
        eta-Csmall*eps-Cbad*(B^2*(∑ ps∈badCompactWords w K eps Y small residue V0 z (expanded w stop P.card v),prefixWeight ps)) ≤
        (B^2/((Y:ℝ)*V0))*countSurvivors Y small residue v := by
  obtain ⟨Cbad,K₀,hCbad,hK₀,hReduction⟩ := uniform_count_error_remainder aStar d eta ha hd heta
  refine ⟨Cbad,K₀,hCbad,hK₀,?_⟩
  intro K hK
  obtain ⟨Csmall,B₀,W,hCsmall,hB₀,hW,hError⟩ := hReduction K hK
  refine ⟨Csmall,B₀,max W 2,hCsmall,hB₀,hW.trans_le (le_max_left _ _),?_⟩
  intro B w top hB hw₀ htop hcomp Y hY z hroot hi h199 h23 hz hcut hclosed hpower residue eps heps stop
  dsimp only
  let P := sourcePrimeSet w top
  let small := LargePrimeDeletion.cutoffPrimes ⌊w⌋₊
  let V0 := SmallSieveFinite.smallEuler ⌊w⌋₊
  let v := rootVertex z ∅ P ((Y:ℝ)*V0)
  have hw : 1 < w := hW.trans_le ((le_max_left _ _).trans hw₀)
  have hw2 : 2 ≤ w := (le_max_right _ _).trans hw₀
  have hV : 0 < V0 := (inv_pos.mpr (zero_lt_one.trans hw)).trans_le (SmallSieveFinite.smallEuler_floor_ge_inv w hw2)
  have hYr : 0 < (Y:ℝ) := by exact_mod_cast hY
  have hmu : 0 < (Y:ℝ)*V0 := mul_pos hYr hV
  have hErrorBound := hError B w top hB ((le_max_left _ _).trans hw₀) htop hcomp Y hY z hroot
    hi h199 h23 hz hcut hclosed hpower residue eps heps (expanded w stop P.card v)
    (expanded_reference_subset w P z ((Y:ℝ)*V0) stop P.card)
  have hPrime : ∀ p∈P,p.Prime := fun p hp => ((mem_sourcePrimeSet (zero_lt_one.trans hw) htop p).mp hp).1
  have hLedger := literal_count_error_ledger w Y small P residue z V0 stop hi hPrime
  have hScaled := mul_le_mul_of_nonneg_left hLedger (show 0 ≤ B^2/((Y:ℝ)*V0) by positivity)
  have hCancel : (B^2/((Y:ℝ)*V0))*(((Y:ℝ)*V0)*referencePolynomial w P z.side z.gap)=
      B^2*referencePolynomial w P z.side z.gap := by field_simp [hmu.ne']
  dsimp only at hErrorBound
  unfold errorSum at hErrorBound
  change B^2*referencePolynomial w P z.side z.gap+
    (B^2/((Y:ℝ)*V0))*(∑ ps∈stopped w stop P.card v,
      (countSurvivors Y small residue (after w v ps)-referenceValue w (after w v ps))) -
    eta-Csmall*eps-Cbad*(B^2*(∑ ps∈badCompactWords w K eps Y small residue V0 z (expanded w stop P.card v),prefixWeight ps)) ≤
    (B^2/((Y:ℝ)*V0))*countSurvivors Y small residue v
  nlinarith
end NumberTheoryLean.StoppedErrorReduction


end Erdos970

end OAI
