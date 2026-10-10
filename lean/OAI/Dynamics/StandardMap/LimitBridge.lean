import OAI.Dynamics.StandardMap.LimitMoments

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
namespace CriticalScaleSequence
lemma bridge_test_bound (S : CriticalScaleSequence) {Rw Rh : ℕ} (B : BridgeGrid Rw Rh)
    (p len : ℕ → ℕ) (Fw : (Fin Rw → ℝ) → ℝ) (Fh : (Fin Rh → ℝ) → ℝ)
    (j : ArrayTestIndex)
    (htest : (∀d,arrayObservation B.sw B.tw Fw d=clippedTest j d) ∨
      (∀d,arrayObservation B.sh B.th Fh d=clippedTest j d))
    (C : ℝ) (hC : ∀ᶠ i in atTop,(∫d,arrayTest j d ∂scaleLaw (S.parameter i) (S.positive i).le (p i) (len i) (S.epsilon i))≤C) :
    ∀ᶠ i in atTop,
      (∫d,arrayObservation B.sw B.tw Fw d ∂scaleLaw (S.parameter i) (S.positive i).le (p i) (len i) (S.epsilon i))≤C ∨
      (∫d,arrayObservation B.sh B.th Fh d ∂scaleLaw (S.parameter i) (S.positive i).le (p i) (len i) (S.epsilon i))≤C := by
  filter_upwards [hC] with i hi
  have hh : (∫d,clippedTest j d ∂scaleLaw (S.parameter i) (S.positive i).le (p i) (len i) (S.epsilon i))≤C := by
    apply le_trans _ hi
    apply integral_mono (integrable_clippedTest _ j)
      ((continuous_arrayTest j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    exact clippedTest_le j
  rcases htest with htest|htest
  · left; simpa only [htest] using hh
  · right; simpa only [htest] using hh
lemma bridge_null_multi (S : CriticalScaleSequence) (K : S.LimitLaws) {Rw Rh : ℕ} (B : BridgeGrid Rw Rh)
    (Fw : (Fin Rw → ℝ) → ℝ) (Fh : (Fin Rh → ℝ) → ℝ) (L : NNReal)
    (hFw : LipschitzWith L Fw) (hFh : LipschitzWith L Fh) (hFwz : Fw 0=0) (hFhz : Fh 0=0)
    (hW0 : ∀d,0≤arrayObservation B.sw B.tw Fw d) (hH0 : ∀d,0≤arrayObservation B.sh B.th Fh d)
    (j : ArrayTestIndex)
    (htest : (∀d,arrayObservation B.sw B.tw Fw d=clippedTest j d) ∨
      (∀d,arrayObservation B.sh B.th Fh d=clippedTest j d))
    (ηw ηh : ℝ) (hηw : 0<ηw) (hηh : 0<ηh) :
    K.multi {d | d.val∈arrayBridgeEvent B Fw Fh ηw ηh}=0 := by
  obtain ⟨C,hC⟩ := S.multiLaw_test_bound j
  exact S.bridge_null_of_limit B (criticalLowerExponent S.offset)
    (fun i => S.exponent i-criticalLowerExponent S.offset i) S.lowerExponent_tendsto
    (fun i j hj => by have := S.lower_lt i; omega) K.multi K.filter K.refines K.multi_converges
    Fw Fh L hFw hFh hFwz hFhz hW0 hH0 C (S.bridge_test_bound B _ _ Fw Fh j htest C hC) ηw ηh hηw hηh
lemma bridge_null_terminal (S : CriticalScaleSequence) (K : S.LimitLaws) {Rw Rh : ℕ} (B : BridgeGrid Rw Rh)
    (Fw : (Fin Rw → ℝ) → ℝ) (Fh : (Fin Rh → ℝ) → ℝ) (L : NNReal)
    (hFw : LipschitzWith L Fw) (hFh : LipschitzWith L Fh) (hFwz : Fw 0=0) (hFhz : Fh 0=0)
    (hW0 : ∀d,0≤arrayObservation B.sw B.tw Fw d) (hH0 : ∀d,0≤arrayObservation B.sh B.th Fh d)
    (j : ArrayTestIndex)
    (htest : (∀d,arrayObservation B.sw B.tw Fw d=clippedTest j d) ∨
      (∀d,arrayObservation B.sh B.th Fh d=clippedTest j d))
    (ηw ηh : ℝ) (hηw : 0<ηw) (hηh : 0<ηh) :
    K.terminal {d | d.val∈arrayBridgeEvent B Fw Fh ηw ηh}=0 := by
  obtain ⟨C,hC⟩ := S.terminalLaw_test_bound j
  exact S.bridge_null_of_limit B S.exponent (fun _ => 1) S.exponent_tendsto
    (fun i j hj => by omega) K.terminal K.filter K.refines K.terminal_converges
    Fw Fh L hFw hFh hFwz hFhz hW0 hH0 C (S.bridge_test_bound B _ _ Fw Fh j htest C hC) ηw ηh hηw hηh
end CriticalScaleSequence
end StandardMapEntropy

end OAI
