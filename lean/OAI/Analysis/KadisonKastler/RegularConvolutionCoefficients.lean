import OAI.Analysis.KadisonKastler.RegularConvolutionOperators

namespace OAI

/-! # Coefficients of the factored convolution operators

These formulas express the constructed action integrals as actual
single and double scalar integrals. They are the comparison formulas
for Haar averages of finite packet matrices.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

private theorem integral_inner_left {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    {F : ℝ → E} (hF : Integrable F volume) (y : E) :
    (∫ t : ℝ, inner ℂ (F t) y) = inner ℂ (∫ t : ℝ, F t) y := by
  have h := congrArg (fun z : ℂ => star z) (integral_inner hF y)
  change (starRingEnd ℂ) (∫ t : ℝ, inner ℂ y (F t)) =
    (starRingEnd ℂ) (inner ℂ y (∫ t : ℝ, F t)) at h
  rw [← integral_conj] at h
  simpa only [inner_conj_symm] using h

private theorem integrable_star_weight (w : ℝ → ℂ) (hw : Integrable w volume) :
    Integrable (fun t => star (w t)) volume := by
  apply hw.norm.mono' hw.aestronglyMeasurable.star
  filter_upwards [] with t
  change ‖star (w t)‖ ≤ ‖w t‖
  exact (norm_star (w t)).le

variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ ξ, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ))

private theorem regularAction_adjoint (t : ℝ) :
    (regularCoreAction U (Multiplicative.ofAdd t) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H).adjoint =
      (regularCoreAction U (Multiplicative.ofAdd (-t)) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
  rw [← ContinuousLinearMap.star_eq_adjoint, ← Unitary.coe_star]
  exact congrArg (fun v : unitary (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) =>
    (v : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))
      (regularGroup_star_eq (regularCoreAction U) t)

include hU in
private theorem integrable_action_vector
    (w : ℝ → ℂ) (hw : Integrable w volume) (f : RegularCoreHilbert H) :
    Integrable (fun t : ℝ => w t •
      (regularCoreAction U (Multiplicative.ofAdd t) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) volume := by
  apply (hw.norm.mul_const ‖f‖).mono'
    (hw.aestronglyMeasurable.smul (continuous_regularCoreAction U hU f).aestronglyMeasurable)
  filter_upwards [] with t
  change ‖w t • (regularCoreAction U (Multiplicative.ofAdd t) :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f‖ ≤ ‖w t‖ * ‖f‖
  rw [norm_smul, Unitary.norm_map]

/-- A coefficient of the action integral, with its adjoint moved to the
test vector. -/
theorem inner_regularActionIntegral
    (w : ℝ → ℂ) (hw : Integrable w volume) (f g : RegularCoreHilbert H) :
    inner ℂ f (regularActionIntegral U hU w hw g) =
      ∫ t : ℝ, w t * inner ℂ
        ((regularCoreAction U (Multiplicative.ofAdd t) :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) g := by
  change inner ℂ f (∫ t : ℝ, w t •
    (regularCoreAction U (Multiplicative.ofAdd (-t)) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) g) = _
  have hi : Integrable (fun t : ℝ => w t •
      (regularCoreAction U (Multiplicative.ofAdd (-t)) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) g) volume := by
    apply (hw.norm.mul_const ‖g‖).mono'
      (hw.aestronglyMeasurable.smul
        ((continuous_regularCoreAction U hU g).comp continuous_neg).aestronglyMeasurable)
    filter_upwards [] with t
    change ‖w t • (regularCoreAction U (Multiplicative.ofAdd (-t)) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) g‖ ≤ ‖w t‖ * ‖g‖
    rw [norm_smul, Unitary.norm_map]
  rw [← integral_inner hi]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [inner_smul_right, ← regularAction_adjoint U t,
    ContinuousLinearMap.adjoint_inner_right]

/-- The adjoint action integral has the positive-translation formula. -/
theorem regularActionIntegral_star_apply
    (w : ℝ → ℂ) (hw : Integrable w volume) (g : RegularCoreHilbert H) :
    star (regularActionIntegral U hU w hw) g =
      ∫ t : ℝ, star (w t) •
        (regularCoreAction U (Multiplicative.ofAdd t) :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) g := by
  have hi := integrable_action_vector U hU (fun t => star (w t))
    (integrable_star_weight w hw) g
  apply ext_inner_left ℂ
  intro f
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (∫ t : ℝ, w t •
    (regularCoreAction U (Multiplicative.ofAdd (-t)) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) g = _
  have hi' : Integrable (fun t : ℝ => w t •
      (regularCoreAction U (Multiplicative.ofAdd (-t)) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) volume := by
    apply (hw.norm.mul_const ‖f‖).mono'
      (hw.aestronglyMeasurable.smul
        ((continuous_regularCoreAction U hU f).comp continuous_neg).aestronglyMeasurable)
    filter_upwards [] with t
    change ‖w t • (regularCoreAction U (Multiplicative.ofAdd (-t)) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f‖ ≤ ‖w t‖ * ‖f‖
    rw [norm_smul, Unitary.norm_map]
  calc
    _ = ∫ t : ℝ, inner ℂ (w t •
        (regularCoreAction U (Multiplicative.ofAdd (-t)) :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) g :=
      (integral_inner_left hi' g).symm
    _ = _ := ?_
  rw [← integral_inner hi]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [inner_smul_left, inner_smul_right, ← regularAction_adjoint U t,
    ContinuousLinearMap.adjoint_inner_left]
  rfl

/-- The two scalar weights and the constant operator are the exact
double-integral kernel of the factored packet convolution. -/
theorem inner_regularPacketConvolution
    (φ ψ : ℝ → ℂ) (hφ : Integrable φ volume) (hψ : Integrable ψ volume)
    (A : H →L[ℂ] H) (f g : RegularCoreHilbert H) :
    inner ℂ f (regularPacketConvolution U hU φ ψ hφ hψ A g) =
      ∫ q : ℝ, φ q * (∫ u : ℝ, star (ψ u) *
        inner ℂ ((regularCoreAction U (Multiplicative.ofAdd q) :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)
          (regularConstantHom (volume : Measure ℝ) A
            ((regularCoreAction U (Multiplicative.ofAdd u) :
              RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) g))) := by
  change inner ℂ f (regularActionIntegral U hU φ hφ
    (regularConstantHom (volume : Measure ℝ) A
      (star (regularActionIntegral U hU ψ hψ) g))) = _
  rw [inner_regularActionIntegral]
  apply integral_congr_ae
  filter_upwards [] with q
  congr 1
  rw [regularActionIntegral_star_apply]
  have hi := integrable_action_vector U hU (fun u => star (ψ u))
    (integrable_star_weight ψ hψ) g
  rw [← (regularConstantHom (volume : Measure ℝ) A).integral_comp_comm hi]
  rw [← integral_inner ((regularConstantHom (volume : Measure ℝ) A).integrable_comp hi)]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [map_smul, inner_smul_right]

end

end KadisonKastler

end OAI
