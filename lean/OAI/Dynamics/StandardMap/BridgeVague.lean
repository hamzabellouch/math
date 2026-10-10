import OAI.Dynamics.StandardMap.BridgeCritical

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
noncomputable def arrayBridgeEvent {Rw Rh : ℕ} (B : BridgeGrid Rw Rh)
    (Fw : (Fin Rw → ℝ) → ℝ) (Fh : (Fin Rh → ℝ) → ℝ) (ηw ηh : ℝ) : Set DistanceArray :=
  {d | (999/1000:ℝ)*((B.v:ℝ)-(B.u:ℝ))<d.val B.u B.v ∧
    ηw<arrayObservation B.sw B.tw Fw d ∧ ηh<arrayObservation B.sh B.th Fh d}
lemma isOpen_arrayBridgeEvent {Rw Rh : ℕ} (B : BridgeGrid Rw Rh)
    (Fw : (Fin Rw → ℝ) → ℝ) (Fh : (Fin Rh → ℝ) → ℝ) (ηw ηh : ℝ)
    (hw : Continuous Fw) (hh : Continuous Fh) : IsOpen (arrayBridgeEvent B Fw Fh ηw ηh) :=
  (isOpen_lt continuous_const (continuous_arrayEval B.u B.v)).inter
    ((isOpen_lt continuous_const (continuous_arrayObservation _ _ _ hw)).inter
      (isOpen_lt continuous_const (continuous_arrayObservation _ _ _ hh)))
namespace CriticalScaleSequence
lemma bridge_vague_tendsto (S : CriticalScaleSequence) {Rw Rh : ℕ} (B : BridgeGrid Rw Rh)
    (p len : ℕ → ℕ) (hp : Tendsto p atTop atTop)
    (hpl : ∀i j,j<len i → p i+j≤S.exponent i)
    (Fw : (Fin Rw → ℝ) → ℝ) (Fh : (Fin Rh → ℝ) → ℝ) (L : NNReal)
    (hFw : LipschitzWith L Fw) (hFh : LipschitzWith L Fh) (hFwz : Fw 0=0) (hFhz : Fh 0=0)
    (hW0 : ∀d,0≤ arrayObservation B.sw B.tw Fw d) (hH0 : ∀d,0≤ arrayObservation B.sh B.th Fh d)
    (T : ℝ) (hT : ∀ᶠ i in atTop,
      (∫d,arrayObservation B.sw B.tw Fw d ∂scaleLaw (S.parameter i) (S.positive i).le (p i) (len i) (S.epsilon i))≤T ∨
      (∫d,arrayObservation B.sh B.th Fh d ∂scaleLaw (S.parameter i) (S.positive i).le (p i) (len i) (S.epsilon i))≤T)
    (ηw ηh : ℝ) (hηw : 0<ηw) (hηh : 0<ηh) (g : C_c(NonAffineArray,ℝ))
    (hg : ∀d,0≤g d) (hz : ∀d : NonAffineArray,d.val∉arrayBridgeEvent B Fw Fh ηw ηh → g d=0) :
    Tendsto (fun i => ∫d,g d ∂nonaffinePart (scaleLaw (S.parameter i) (S.positive i).le (p i) (len i) (S.epsilon i))) atTop (𝓝 0) := by
  let F := arrayTestExtend g
  obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn F.continuous.continuousOn
  have hFz : ∀d,d∉arrayBridgeEvent B Fw Fh ηw ηh → F d=0 := by
    intro d hd
    by_cases ha : d∈affineLocus
    · exact arrayTestExtend_affine g d ha
    · exact (arrayTestExtend_apply g ⟨d,ha⟩).trans (hz ⟨d,ha⟩ hd)
  have hF0 : ∀d,0≤F d := by
    intro d
    by_cases ha : d∈affineLocus
    · rw [show F d=0 from arrayTestExtend_affine g d ha]
    · rw [arrayTestExtend_apply g ⟨d,ha⟩]; exact hg _
  have hFB : ∀d,F d≤ max C 0 := by
    intro d
    have hb : |F d|≤C := by convert! hC d (mem_univ d) using 1
    exact (le_abs_self _).trans (hb.trans (le_max_left _ _))
  have hFW : ∀d,F d≤(max C 0/ηw)*arrayObservation B.sw B.tw Fw d := by
    intro d
    by_cases hd : d∈arrayBridgeEvent B Fw Fh ηw ηh
    · have hpos := hd.2.1
      have hh := mul_le_mul_of_nonneg_left hpos.le (div_nonneg (le_max_right C 0) hηw.le)
      rw [div_mul_cancel₀ _ hηw.ne'] at hh
      exact (hFB d).trans hh
    · rw [hFz d hd]
      exact mul_nonneg (div_nonneg (le_max_right _ _) hηw.le) (hW0 d)
  have hzero : ∀d,¬((999/1000:ℝ)*((B.v:ℝ)-(B.u:ℝ))<d.val B.u B.v ∧ ηh<arrayObservation B.sh B.th Fh d) → F d=0 := by
    intro d hd
    apply hFz
    exact fun h => hd ⟨h.1,h.2.2⟩
  have hh := S.bridge_integral_tendsto B p len hp hpl Fw Fh L hFw hFh hFwz hFhz hW0 hH0 T hT
    ηh hηh F F.continuous hF0 (max C 0/ηw) (div_nonneg (le_max_right _ _) hηw.le) hFW hzero
  simpa only [F,integral_arrayTestExtend] using hh
lemma bridge_null_of_limit (S : CriticalScaleSequence) {Rw Rh : ℕ} (B : BridgeGrid Rw Rh)
    (p len : ℕ → ℕ) (hp : Tendsto p atTop atTop)
    (hpl : ∀i j,j<len i → p i+j≤S.exponent i)
    (ν : Measure NonAffineArray) [ν.Regular] (l : Filter ℕ) [l.NeBot] (hl : l≤atTop)
    (hconv : ∀g : C_c(NonAffineArray,ℝ),Tendsto (fun i => ∫d,g d ∂nonaffinePart
      (scaleLaw (S.parameter i) (S.positive i).le (p i) (len i) (S.epsilon i))) l (𝓝 (∫d,g d ∂ν)))
    (Fw : (Fin Rw → ℝ) → ℝ) (Fh : (Fin Rh → ℝ) → ℝ) (L : NNReal)
    (hFw : LipschitzWith L Fw) (hFh : LipschitzWith L Fh) (hFwz : Fw 0=0) (hFhz : Fh 0=0)
    (hW0 : ∀d,0≤arrayObservation B.sw B.tw Fw d) (hH0 : ∀d,0≤arrayObservation B.sh B.th Fh d)
    (T : ℝ) (hT : ∀ᶠ i in atTop,
      (∫d,arrayObservation B.sw B.tw Fw d ∂scaleLaw (S.parameter i) (S.positive i).le (p i) (len i) (S.epsilon i))≤T ∨
      (∫d,arrayObservation B.sh B.th Fh d ∂scaleLaw (S.parameter i) (S.positive i).le (p i) (len i) (S.epsilon i))≤T)
    (ηw ηh : ℝ) (hηw : 0<ηw) (hηh : 0<ηh) :
    ν {d | d.val∈arrayBridgeEvent B Fw Fh ηw ηh}=0 := by
  apply vague_open_null l _ ν hconv ((isOpen_arrayBridgeEvent B Fw Fh ηw ηh hFw.continuous hFh.continuous).preimage continuous_subtype_val)
  intro g hg hz
  exact (S.bridge_vague_tendsto B p len hp hpl Fw Fh L hFw hFh hFwz hFhz hW0 hH0 T hT ηw ηh hηw hηh g hg hz).mono_left hl
end CriticalScaleSequence
end StandardMapEntropy

end OAI
