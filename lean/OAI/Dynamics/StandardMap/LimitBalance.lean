import OAI.Dynamics.StandardMap.ArrayTopology

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Topology
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
lemma scaleLaw_one (k : ℝ) (hk : 0 ≤ k) (p : ℕ) (ε : ℝ) :
    scaleLaw k hk p 1 ε=ENNReal.ofReal (1/ε) • sampleLaw k hk (2^p) (by positivity) := by
  simp [scaleLaw]
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (L : S.LimitLaws)
lemma law_dilation_balance (i : ℕ) :
    (S.multiLaw i).map arrayDilate+S.initialLaw i=S.multiLaw i+S.terminalLaw i := by
  unfold multiLaw initialLaw terminalLaw
  rw [scaleLaw_one,scaleLaw_one]
  convert! scaleLaw_dilate_boundary (S.parameter i) (S.positive i).le
    (criticalLowerExponent S.offset i) (S.exponent i-criticalLowerExponent S.offset i) (S.epsilon i) using 1
  rw [Nat.add_sub_of_le (S.lower_lt i).le]
lemma integral_law_dilation_balance (i : ℕ) (g : C_c(NonAffineArray,ℝ)) :
    (∫ d,(g.comp nonaffineDilation) d ∂nonaffinePart (S.multiLaw i))+
      (∫ d,g d ∂nonaffinePart (S.initialLaw i))=
      (∫ d,g d ∂nonaffinePart (S.multiLaw i))+(∫ d,g d ∂nonaffinePart (S.terminalLaw i)) := by
  rw [←integral_arrayTestExtend,←integral_arrayTestExtend,←integral_arrayTestExtend,←integral_arrayTestExtend]
  simp_rw [arrayTestExtend_dilate]
  rw [← integral_map (f := fun d => arrayTestExtend g d) continuous_arrayDilate.measurable.aemeasurable (arrayTestExtend g).continuous.aestronglyMeasurable]
  have hi (μ : Measure DistanceArray) [IsFiniteMeasure μ] : Integrable (fun d => arrayTestExtend g d) μ :=
    (arrayTestExtend g).continuous.integrable_of_hasCompactSupport (arrayTestExtend g).hasCompactSupport
  rw [← integral_add_measure (hi _) (hi _),← integral_add_measure (hi _) (hi _),S.law_dilation_balance i]
lemma integral_dilation_balance (g : C_c(NonAffineArray,ℝ)) :
    (∫ d,g (nonaffineDilate d) ∂L.multi)=(∫ d,g d ∂L.multi)+(∫ d,g d ∂L.terminal) := by
  have ht := (L.multi_converges (g.comp nonaffineDilation)).add ((S.initial_vague_zero g).mono_left L.refines)
  rw [add_zero] at ht
  apply tendsto_nhds_unique ht
  have hh := (L.multi_converges g).add (L.terminal_converges g)
  exact hh.congr (fun i => (S.integral_law_dilation_balance i g).symm)
instance multi_dilate_local : IsFiniteMeasureOnCompacts (L.multi.map nonaffineDilate) where
  lt_top_of_isCompact K hK := by
    rw [Measure.map_apply continuous_nonaffineDilate.measurable hK.isClosed.measurableSet]
    exact (proper_nonaffineDilate.isCompact_preimage hK).measure_lt_top
instance multi_terminal_local : IsFiniteMeasureOnCompacts (L.multi+L.terminal) where
  lt_top_of_isCompact K hK := by
    rw [Measure.add_apply]
    exact ENNReal.add_lt_top.mpr ⟨hK.measure_lt_top,hK.measure_lt_top⟩
lemma dilation_balance : L.multi.map nonaffineDilate=L.multi+L.terminal := by
  let : IsFiniteMeasureOnCompacts (L.multi+L.terminal) := S.multi_terminal_local L
  let : IsLocallyFiniteMeasure (L.multi+L.terminal) := inferInstance
  let : (L.multi+L.terminal).Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro g
  rw [integral_map (f := fun d => g d) continuous_nonaffineDilate.measurable.aemeasurable g.continuous.aestronglyMeasurable,
    integral_add_measure (f := fun d => g d) (g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport)
      (g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport)]
  exact S.integral_dilation_balance L g
end CriticalScaleSequence
end StandardMapEntropy

end OAI
