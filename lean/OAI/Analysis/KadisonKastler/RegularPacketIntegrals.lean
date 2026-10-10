import OAI.Analysis.KadisonKastler.RegularCommutantPackets

namespace OAI

/-! # Integral formulas for wave-packet compression

The adjoint of a scalar packet is its ordinary vector integral. The
gauged formula inserts the original unitary group inside that integral.
Both integrability assertions follow from the actual `L²` bounds.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

omit [CompleteSpace H] in
theorem integrable_scalarPacket_pair
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (f : RegularCoreHilbert H) :
    Integrable (fun t => star (φ t) • f t) volume := by
  have hi := (Lp.memLp φ).norm.integrable_mul (Lp.memLp f).norm
  apply hi.mono' ((Lp.aestronglyMeasurable φ).star.smul (Lp.aestronglyMeasurable f))
  filter_upwards [] with t
  change ‖star (φ t) • f t‖ ≤ ‖φ t‖ * ‖f t‖
  rw [norm_smul, norm_star]

/-- Scalar packet compression is the usual vector-valued integral. -/
theorem regularTensorVector_adjoint_apply
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (f : RegularCoreHilbert H) :
    (regularTensorVector φ).adjoint f = ∫ t : ℝ, star (φ t) • f t := by
  apply ext_inner_left ℂ
  intro η
  rw [ContinuousLinearMap.adjoint_inner_right,
    ← integral_inner (integrable_scalarPacket_pair φ f), L2.inner_def]
  apply integral_congr_ae
  filter_upwards [regularTensorVector_apply_ae φ η] with t ht
  rw [ht]
  simp only [inner_smul_left, inner_smul_right]
  rfl

variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ ξ, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ))

include hU in
theorem integrable_gaugedPacket_pair
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (f : RegularCoreHilbert H) :
    Integrable (fun t => star (φ t) •
      (U (Multiplicative.ofAdd t) : H →L[ℂ] H) (f t)) volume := by
  apply (integrable_scalarPacket_pair φ
    ((regularGauge U hU : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)).congr
  filter_upwards [regularGauge_apply_ae U hU f] with t ht
  exact congrArg (fun x : H => star (φ t) • x) ht

/-- The adjoint of a gauged packet integrates the untwisted vector field. -/
theorem regularGaugedPacket_adjoint_apply
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (f : RegularCoreHilbert H) :
    (regularGaugedPacket U hU φ).adjoint f =
      ∫ t : ℝ, star (φ t) • (U (Multiplicative.ofAdd t) : H →L[ℂ] H) (f t) := by
  have he : (regularGaugedPacket U hU φ).adjoint f =
      (regularTensorVector φ).adjoint
        ((regularGauge U hU : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) := by
    change (((star (regularGauge U hU) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H).comp
        (regularTensorVector φ)).adjoint) f = _
    simp only [ContinuousLinearMap.adjoint_comp, ← ContinuousLinearMap.star_eq_adjoint,
      ← Unitary.coe_star, star_star, ContinuousLinearMap.comp_apply]
  rw [he, regularTensorVector_adjoint_apply]
  apply integral_congr_ae
  filter_upwards [regularGauge_apply_ae U hU f] with t ht
  exact congrArg (fun x : H => star (φ t) • x) ht

end

end KadisonKastler

end OAI
