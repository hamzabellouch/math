import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkResidueRootAverage
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSelectedIntegralReplacementTests

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSelectedPrincipalAmplitude
open Construction HistoryBulkSelectedIntegralReplacement HistoryBulkResidueRootAverage
open HistoryBulkResidueNormSum HistoryBulkSpectatorProduct HistoryBulkReplacementGeometry
open HistoryFrequencyResidues HistoryCRTIntegration

theorem norm_rootTest_le (independent mixed : Bool) (d : Decomposition)
    {l m : ℕ} {V : ℕ → ℕ} {outside : List ℕ} (h g : History l)
    (hs : h.Supported V outside) (gs : g.Supported V outside)
    (hp : ∀ q ∈ outside, q.Prime) (hV : ∀ q ∈ outside, ∀ j ≤ l, V j < q)
    (σ : Equiv.Perm (Fin (2^l) × Fin m)) (K : ℕ)
    (x : Fin (2^l) × Fin m → (ZMod (bulkModulus h g outside K))ˣ) :
    ‖rootTest independent mixed d h g hs gs hp hV σ K x‖ ≤
      (outside.prod : ℝ)^(2^(l+1)) := by
  let : NeZero outside.prod := HistorySignedSpectatorDiagramAverage.outsideNeZero hp
  let : NeZero (pairedFrequencyProduct h g) := ⟨pairedFrequencyProduct_ne_zero hs gs⟩
  cases independent <;> cases mixed
  · change ‖canonicalUnit d h g hs gs hp hV σ K x‖ ≤ _
    unfold canonicalUnit
    apply norm_average_le
    intro zD
    apply norm_average_le
    intro zR
    exact canonicalUnitTest_norm_le d h g hs gs hp hV σ K _ _ _ zD zR x
  · change ‖canonicalMixed d h g hs gs hp hV σ K x‖ ≤ _
    unfold canonicalMixed
    apply norm_average_le
    intro zD
    apply norm_average_le
    intro zR
    exact canonicalMixedTest_norm_le d h g hs gs hp hV σ K _ _ _ zD zR x
  · change ‖independentUnit d h g hs gs hp hV σ K x‖ ≤ _
    unfold independentUnit
    apply norm_average_le
    intro zD
    apply norm_average_le
    intro zR
    exact independentUnitTest_norm_le d h g hs gs hp hV σ K _ _ _ zD zR x
  · change ‖independentMixed d h g hs gs hp hV σ K x‖ ≤ _
    unfold independentMixed
    apply norm_average_le
    intro zD
    apply norm_average_le
    intro zR
    exact independentMixedTest_norm_le d h g hs gs hp hV σ K _ _ _ zD zR x

end Ostmann.Arithmetic.HistoryBulkSelectedPrincipalAmplitude

end

end OAI
