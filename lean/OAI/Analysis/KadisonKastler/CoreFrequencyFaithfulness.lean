import OAI.Analysis.KadisonKastler.CoreWindowPackets
import OAI.Analysis.KadisonKastler.BoundaryFiniteIsomorphism
import OAI.Analysis.FactorGeneration.HilbertLimits

namespace OAI

/-! # Faithfulness of the bounded-frequency vector on its corner

Spectral multipliers of the regular action give localized scalar packets.
The original commutant fills their vector coordinates, proving that an
operator in the core which kills the trace packet vanishes on its window.
No traciality or finiteness assertion is made here.
-/

namespace KadisonKastler

open MeasureTheory UnitalTomsWinter
open scoped ENNReal

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
  (M : VonNeumannAlgebra H)
  (hM : ∀ s a, a ∈ M → unitaryConj (U s) a ∈ M)
  (Ω : H) (hΩ : ∀ t, (U t : H →L[ℂ] H) Ω = Ω)

include hM hΩ in
theorem core_kills_unit_packet_of_kills_trace_packet
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT : T ∈ regularCoreAlgebra U hU M)
    (hz : T (coreTraceFrequencyVector Ω) = 0) : T (unitFrequencyVector Ω) = 0 := by
  have hc := VonNeumannAlgebra.mem_commutant_iff.mp
    (regularActionMultiplier_mem_commutant U hU M hM coreTraceReciprocal
      coreTraceReciprocal_measurable (Real.exp Real.pi) coreTraceReciprocal_bound) T hT
  have he := congrArg (fun A : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H =>
    A (coreTraceFrequencyVector Ω)) hc
  change T (regularActionMultiplier U hU coreTraceReciprocal
    coreTraceReciprocal_measurable (Real.exp Real.pi) coreTraceReciprocal_bound
      (coreTraceFrequencyVector Ω)) = _ at he
  rw [coreTraceReciprocal_packet U hU Ω hΩ, mul_apply_eq_comp, hz, map_zero] at he
  exact he

include hM hΩ in
theorem core_kills_window_of_kills_unit_packet
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT : T ∈ regularCoreAlgebra U hU M)
    (hz : T (unitFrequencyVector Ω) = 0) :
    T * regularFrequencyWindow 0 1 = 0 := by
  have hfixed := ((mem_fixedPointAlgebra_iff _ _ _).mp
    (regularCoreAlgebra_le_fixed U hU M hM hT)).2
  have hconst := (mem_regularTensorAlgebra_iff M T).mp
    (regularCoreAlgebra_le_tensor U hU M hM hT)
  have hdense : DenseRange (fun b : Algebra M.commutant => b.val Ω) :=
    Generator.commutant_orbit_dense M Ω (fun a ha => by
      apply hsep
      exact ha)
  have hpacket (s : Set ℝ) (hs : MeasurableSet s) (x : H) :
      T (regularFrequencyPacket (regularIndicatorProjection s hs unitFrequencyScalar) x) = 0 := by
    let φ := s.indicator (fun _ => (1 : ℂ))
    have hb (t : ℝ) : ‖φ t‖ ≤ 1 := by
      by_cases ht : t ∈ s <;> simp [φ, ht]
    have hc := commute_regularActionMultiplier_of_fixed U hU T hfixed φ
      (measurable_const.indicator hs) 1 hb
    have he := congrArg (fun A : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H =>
      A (unitFrequencyVector Ω)) hc.eq
    have hzero : T
        (regularFrequencyPacket (regularIndicatorProjection s hs unitFrequencyScalar) Ω) = 0 := by
      change T (regularActionMultiplier U hU φ (measurable_const.indicator hs) 1 hb
        (regularFrequencyPacket unitFrequencyScalar Ω)) = _ at he
      rw [regularActionMultiplier_packet U hU Ω hΩ] at he
      change T (regularFrequencyPacket (regularIndicatorProjection s hs unitFrequencyScalar) Ω) =
        regularActionMultiplier U hU φ (measurable_const.indicator hs) 1 hb
          (T (unitFrequencyVector Ω)) at he
      simpa only [hz, map_zero] using he
    have hh : (fun y : H => T (regularFrequencyPacket
        (regularIndicatorProjection s hs unitFrequencyScalar) y)) = fun _ => 0 := by
      apply hdense.equalizer
      · exact T.continuous.comp ((Lp.fourierTransformₗᵢ ℝ H).symm.continuous.comp
          (regularTensorVector _).continuous)
      · exact continuous_const
      · funext b
        change T (regularFrequencyPacket
          (regularIndicatorProjection s hs unitFrequencyScalar) (b.val Ω)) = 0
        rw [← regularConstantHom_frequencyPacket]
        have hb' := congrArg (fun A : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H =>
          A (regularFrequencyPacket (regularIndicatorProjection s hs unitFrequencyScalar) Ω))
          (hconst b.val b.property)
        change regularConstantHom volume b.val
          (T (regularFrequencyPacket (regularIndicatorProjection s hs unitFrequencyScalar) Ω)) =
          T (regularConstantHom volume b.val
            (regularFrequencyPacket (regularIndicatorProjection s hs unitFrequencyScalar) Ω)) at hb'
        rw [← hb', hzero, map_zero]
    exact congrFun hh x
  have hall (f : RegularCoreHilbert H) :
      T (regularFrequencyWindow 0 1 ((Lp.fourierTransformₗᵢ ℝ H).symm f)) = 0 := by
    induction f using Lp.induction (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) with
    | @indicatorConst x s hs hfin =>
        rw [Lp.simpleFunc.coe_indicatorConst, unitWindow_indicator_packet s hs hfin.ne]
        exact hpacket s hs x
    | @add f g hf hg hdis hF hG =>
        simp only [map_add, hF, hG, add_zero]
    | isClosed =>
        exact isClosed_eq (T.continuous.comp ((regularFrequencyWindow 0 1).continuous.comp
          (Lp.fourierTransformₗᵢ ℝ H).symm.continuous)) continuous_const
  apply ContinuousLinearMap.ext
  intro f
  change T (regularFrequencyWindow 0 1 f) = 0
  simpa only [LinearIsometryEquiv.symm_apply_apply] using
    hall ((Lp.fourierTransformₗᵢ ℝ H) f)

include hM hΩ in
theorem core_kills_window_of_kills_trace_packet
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT : T ∈ regularCoreAlgebra U hU M)
    (hz : T (coreTraceFrequencyVector Ω) = 0) :
    T * regularFrequencyWindow 0 1 = 0 :=
  core_kills_window_of_kills_unit_packet U hU M hM Ω hΩ hsep T hT
    (core_kills_unit_packet_of_kills_trace_packet U hU M hM Ω hΩ T hT hz)

end

end KadisonKastler

end OAI
