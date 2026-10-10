import OAI.NumberTheory.Jacobsthal.Partitions.SourceCanonicalKeyGeometry

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace Erdos970Final
open _root_.Filter NumberTheoryLean NumberTheoryLean.PrimeHistories
  NumberTheoryLean.SourceCanonicalKeyGeometry NumberTheoryLean.CanonicalStopPartition
  NumberTheoryLean.SourceStopPredicate NumberTheoryLean.StoppedCountVertex
  NumberTheoryLean.StoppedCountAdapters NumberTheoryLean.StoppedVertexHistory
  NumberTheoryLean.StoppedTraceSets NumberTheoryLean.LogarithmicBinEndpoints
  NumberTheoryLean.LogarithmicBinLabels NumberTheoryLean.LogarithmicBinPartition
  NumberTheoryLean.LargePrimeDeletion
  ErdosInverseBoxHeight ErdosCorrectionLimit ErdosSourceReferenceMargin ErdosStoppedArithmetic

attribute [local instance] Classical.propDecidable

theorem source_stopped_correction :
    ∃ eta0 : ℝ,0 < eta0 ∧ eta0 ≤ 1/4 ∧ ∀ Cs : ℝ,0 ≤ Cs →
      ∃ K : ℝ,0 < K ∧ ∀ Clen : ℝ,0 ≤ Clen → ∀ eta : ℝ,0 ≤ eta → eta ≤ eta0 →
      ∀ xi : ℝ,∀ hxi : 0 < xi,xi ≤ 1 → ∀ rho : ℝ,1 < rho →
      ∀ᶠ top : ℝ in atTop,∃ hw : 1 < sourceW top,∃ htop : sourceW top < top,
      ∀ a : ℕ → ℕ,
      let w := sourceW top
      let B := sourceB top
      let Y := sourceY top
      let mu := (Y : ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊
      let z := sourceRootNode (1/100) top
      let P := sourcePrimeSet w top
      let v := rootVertex z ∅ P mu
      let stop := stopCandidate Y w Cs eta Clen B xi ((2*K)*(Real.log w)^2)
        (rho*(2*K)*(Real.log w)^2) (lower w top xi) (width w top xi)
        (label (zero_lt_one.trans hw) htop hxi) a z
      0 ≤ ∑ ps ∈ stopped w stop P.card v,
        (countSurvivors Y (cutoffPrimes ⌊w⌋₊) a (after w v ps)-referenceValue w (after w v ps)) := by
  obtain ⟨eta0,heta0,heta01,P0,_hP0,hArithmetic⟩ := canonical_key_correction_nonnegative
  refine ⟨eta0,heta0,heta01,?_⟩
  intro Cs hCs
  obtain ⟨K,hK,hArithmetic⟩ := hArithmetic Cs hCs
  refine ⟨K,hK,?_⟩
  intro Clen hClen eta heta hetaU xi hxi hxi1 rho hrho
  have hKstop : 0 < 2*K := by positivity
  obtain ⟨W,_hW,hArithmetic⟩ := hArithmetic (2*rho) xi (by linarith) hxi
  have hGeometry := source_key_geometry hClen hxi hxi1 hKstop (by linarith : 0 < rho) P0
  filter_upwards [hGeometry,rootW_tendsto.eventually_ge_atTop W] with top hGeometry hW
  dsimp only at hGeometry
  obtain ⟨hY,hw,htop,hGeometry⟩ := hGeometry
  refine ⟨hw,htop,?_⟩
  intro a
  dsimp only
  apply stopped_correction_of_key_signs (sourceY top) (sourceW top) top Cs eta Clen
    (sourceB top) xi ((2*K)*(Real.log (sourceW top))^2) (rho*(2*K)*(Real.log (sourceW top))^2)
    ((sourceY top : ℝ)*SmallSieveFinite.smallEuler ⌊sourceW top⌋₊) hw htop hxi hClen a
    (sourceRootNode (1/100) top)
  intro k hk
  obtain ⟨⟨d⟩,hPsize,hPl,hPu,hWidthLo,hWidthHi,hBand,hRef⟩ := hGeometry Cs eta a k hk
  have hPl' : Real.exp (K*(Real.log (sourceW top))^3) ≤ (k.tail.getLastD 0 : ℝ) := by
    simpa only [show (2*K)/2=K by ring] using hPl
  have hPu' : (k.tail.getLastD 0 : ℝ) ≤ Real.exp ((2*rho)*K*(Real.log (sourceW top))^3) := by
    convert hPu using 1
    congr 1
    ring
  apply hArithmetic (sourceW top) hW top hw htop (sourceY top) hY eta Clen (sourceB top)
    ((2*K)*(Real.log (sourceW top))^2) (rho*(2*K)*(Real.log (sourceW top))^2)
    ((sourceY top : ℝ)*SmallSieveFinite.smallEuler ⌊sourceW top⌋₊) heta hetaU a
    (sourceRootNode (1/100) top) k d hPsize hPl' hPu' hWidthLo hWidthHi
  · simpa only [ErdosCommonMInterval.lengthExponent,ErdosCommonMInterval.referenceLength] using hBand
  · exact hRef

end Erdos970Final


end Erdos970

end OAI
