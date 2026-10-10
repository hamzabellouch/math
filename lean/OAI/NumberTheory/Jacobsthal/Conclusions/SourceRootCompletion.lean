import OAI.NumberTheory.Jacobsthal.Estimates.SourceRootErrorLower
import OAI.NumberTheory.Jacobsthal.Paths.SourceStoppedCorrection

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace Erdos970Final
open _root_.Filter NumberTheoryLean NumberTheoryLean.PrimeHistories
  NumberTheoryLean.SourceRootErrorLower NumberTheoryLean.StoppedCountVertex
  NumberTheoryLean.StoppedCountAdapters NumberTheoryLean.LogarithmicBinPartition
  NumberTheoryLean.LargePrimeDeletion
  ErdosInverseBoxHeight ErdosCorrectionLimit


theorem source_root_survivor_lower : ∃ c : ℝ,0 < c ∧ ∀ᶠ top : ℝ in atTop,
    ∀ a : ℕ → ℕ,
    c*((sourceY top : ℝ)*SmallSieveFinite.smallEuler ⌊sourceW top⌋₊/(sourceB top)^2) ≤
      countSurvivors (sourceY top) (cutoffPrimes ⌊sourceW top⌋₊) a
        (rootVertex (sourceRootNode (1/100) top) ∅ (sourcePrimeSet (sourceW top) top)
          ((sourceY top : ℝ)*SmallSieveFinite.smallEuler ⌊sourceW top⌋₊)) := by
  obtain ⟨eta0,heta0,heta01,hCorrection⟩ := source_stopped_correction
  obtain ⟨c,Clen,Cs,xi0,hc,hClen,hCs,_hCsMin,hxi0,hxi01,hError⟩ :=
    source_root_lower_with_stopped_correction 1
  have hClenPos : 0 < Clen := by linarith
  obtain ⟨K,hK,hCorrection⟩ := hCorrection Cs hCs.le
  let eta : ℝ := eta0/2
  let xi : ℝ := min (xi0/2) (1/(40*Clen))
  have heta : 0 < eta := by dsimp [eta];positivity
  have hetaU : eta ≤ eta0 := by dsimp [eta];linarith
  have hetaHalf : eta < 1/2 := by dsimp [eta];linarith
  have hxi : 0 < xi := lt_min (by positivity) (by positivity)
  have hxiU : xi ≤ xi0 := (min_le_left _ _).trans (by linarith)
  have hxi1 : xi ≤ 1 := hxiU.trans hxi01
  obtain ⟨rho,hrho,hError⟩ := hError eta heta hetaHalf xi hxi hxiU
  have hKstop : 0 < 2*K := by positivity
  have hCorrection := hCorrection Clen hClenPos.le eta heta.le hetaU xi hxi hxi1 rho (by linarith)
  refine ⟨c,hc,?_⟩
  filter_upwards [hError (2*K) hKstop,hCorrection] with top hError hCorrection
  obtain ⟨_hw,_htop,hError⟩ := hError
  obtain ⟨_hwC,_htopC,hCorrection⟩ := hCorrection
  intro a
  have hLower := hError a
  have hSign := hCorrection a
  dsimp only at hLower hSign
  linarith

end Erdos970Final


end Erdos970

end OAI
