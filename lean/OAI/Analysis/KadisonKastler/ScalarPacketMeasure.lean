import OAI.Analysis.KadisonKastler.RegularCommutantPackets
import OAI.Analysis.KadisonKastler.RegularPacketLocalization
import OAI.Analysis.KadisonKastler.StateActionAverages

namespace OAI

/-! # The probability measure and action average of a scalar packet -/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

def scalarPacketMeasure (φ : Lp ℂ 2 (volume : Measure ℝ)) : Measure ℝ :=
  volume.withDensity (fun t => ENNReal.ofReal (‖φ t‖^2))

theorem scalarPacketMeasure_univ (φ : Lp ℂ 2 (volume : Measure ℝ)) :
    scalarPacketMeasure φ Set.univ=ENNReal.ofReal (‖φ‖^2) := by
  rw [scalarPacketMeasure,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal
      ((Lp.memLp φ).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
      (Eventually.of_forall fun t => sq_nonneg ‖φ t‖),regular_integral_norm_sq]

theorem scalarPacketMeasure_probability (φ : Lp ℂ 2 (volume : Measure ℝ)) (hφ : ‖φ‖=1) :
    IsProbabilityMeasure (scalarPacketMeasure φ) := by
  constructor
  rw [scalarPacketMeasure_univ,hφ]
  norm_num

theorem integral_scalarPacketMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (f : ℝ → E) :
    (∫ t, f t ∂scalarPacketMeasure φ)=∫ t, (‖φ t‖^2) • f t := by
  rw [scalarPacketMeasure,integral_withDensity_eq_integral_toReal_smul
    ((Lp.stronglyMeasurable φ).measurable.norm.pow_const 2 |>.ennreal_ofReal)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  funext t
  rw [ENNReal.toReal_ofReal (sq_nonneg _)]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

def scalarPacketAverage (φ : Lp ℂ 2 (volume : Measure ℝ)) (hφ : ‖φ‖=1)
    (T : H →L[ℂ] H) : H →L[ℂ] H := by
  let : IsProbabilityMeasure (scalarPacketMeasure φ) := scalarPacketMeasure_probability φ hφ
  exact stateActionAverage U hU (scalarPacketMeasure φ) T

theorem scalarPacketAverage_coefficient
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (hφ : ‖φ‖=1) (T : H →L[ℂ] H) (ξ : H) :
    inner ℂ ξ (scalarPacketAverage U hU φ hφ T ξ)=
      ∫ t, (‖φ t‖^2) • inner ℂ ξ (stateActionOrbit U T t ξ) := by
  let : IsProbabilityMeasure (scalarPacketMeasure φ) := scalarPacketMeasure_probability φ hφ
  have hi := integrable_bounded_operator_vector (scalarPacketMeasure φ) (stateActionOrbit U T)
    (fun x => (stateActionOrbit_continuous U hU T x).aestronglyMeasurable)
    (Eventually.of_forall fun t => (stateActionOrbit_norm U T t).le) ξ
  change (innerSL ℂ ξ) (∫ t, stateActionOrbit U T t ξ ∂scalarPacketMeasure φ)=_
  rw [← (innerSL ℂ ξ).integral_comp_comm hi,integral_scalarPacketMeasure]
  rfl

theorem scalarPacketAverage_strongly_invariant
    (ψ : (H →L[ℂ] H) →L[ℂ] ℂ)
    (hψ : ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : H →L[ℂ] H),
      ψ (stateActionAverage U hU μ T)=ψ T)
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (hφ : ‖φ‖=1) (T : H →L[ℂ] H) :
    ψ (scalarPacketAverage U hU φ hφ T)=ψ T := by
  let : IsProbabilityMeasure (scalarPacketMeasure φ) := scalarPacketMeasure_probability φ hφ
  exact hψ (scalarPacketMeasure φ) T

theorem regularGaugedPacket_coefficient
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (hφ : ‖φ‖=1) (T : H →L[ℂ] H) (ξ : H) :
    inner ℂ (regularGaugedPacket U hU φ ξ)
      (regularConstantHom volume T (regularGaugedPacket U hU φ ξ))=
        inner ℂ ξ (scalarPacketAverage U hU φ hφ T ξ) := by
  rw [scalarPacketAverage_coefficient,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [regularGaugedPacket_apply_ae U hU φ ξ,
    regularConstantHom_apply_ae (volume : Measure ℝ) T (regularGaugedPacket U hU φ ξ)] with t hf hT
  rw [hT,hf,map_smul,map_smul,inner_smul_left,inner_smul_right]
  have hi : inner ℂ
      ((star (U (Multiplicative.ofAdd t)) : H →L[ℂ] H) ξ)
      (T ((star (U (Multiplicative.ofAdd t)) : H →L[ℂ] H) ξ))=
      inner ℂ ξ (stateActionOrbit U T t ξ) := by
    change inner ℂ (star (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ)
      (T (star (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ))=
      inner ℂ ξ ((U (Multiplicative.ofAdd t) : H →L[ℂ] H)
        (T (star (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ)))
    exact ContinuousLinearMap.adjoint_inner_left _ _ _
  rw [hi]
  change star (φ t)*(φ t*inner ℂ ξ (stateActionOrbit U T t ξ))=
    ((‖φ t‖^2 : ℝ) : ℂ)*inner ℂ ξ (stateActionOrbit U T t ξ)
  rw [← mul_assoc,Complex.star_def,Complex.conj_mul',Complex.ofReal_pow]

end

end KadisonKastler

end OAI
