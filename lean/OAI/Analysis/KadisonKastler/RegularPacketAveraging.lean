import OAI.Analysis.KadisonKastler.RegularPacketFubini
import OAI.Analysis.KadisonKastler.RegularConvolutionCoefficients

namespace OAI

/-! # Haar averages of finite packet operators

The packet and convolution expressions are the same absolutely
integrable three-variable kernel, with the integrations reordered.
Thus every averaged packet matrix with a commutant coefficient belongs
to the concrete generated commutant algebra.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

private theorem inner_integrals (F G : ℝ → H)
    (hF : Integrable F volume) (hG : Integrable G volume) (A : H →L[ℂ] H) :
    inner ℂ (∫ q : ℝ, F q) (A (∫ u : ℝ, G u)) =
      ∫ q : ℝ, ∫ u : ℝ, inner ℂ (F q) (A (G u)) := by
  have hleft (y : H) :
      (∫ q : ℝ, inner ℂ (F q) y) = inner ℂ (∫ q : ℝ, F q) y := by
    have h := congrArg (fun z : ℂ => star z) (integral_inner hF y)
    change (starRingEnd ℂ) (∫ q : ℝ, inner ℂ y (F q)) =
      (starRingEnd ℂ) (inner ℂ y (∫ q : ℝ, F q)) at h
    rw [← integral_conj] at h
    simpa only [inner_conj_symm] using h
  rw [← hleft]
  apply integral_congr_ae
  filter_upwards [] with q
  rw [← A.integral_comp_comm hG, integral_inner (A.integrable_comp hG)]

variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ ξ, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ))

include hU in
private theorem integrable_packet_translate
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (f : RegularCoreHilbert H) (r : ℝ) :
    Integrable (fun q : ℝ => star (φ q) •
      (U (Multiplicative.ofAdd q) : H →L[ℂ] H) (f (r + q))) volume := by
  apply (integrable_gaugedPacket_pair U hU φ (regularTranslateApply r f)).congr
  filter_upwards [regularTranslateApply_ae r f] with q hq
  rw [hq, add_comm q r]

private theorem packet_adjoint_translate
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (f : RegularCoreHilbert H) (r : ℝ) :
    (regularGaugedPacket U hU φ).adjoint (regularTranslateApply r f) =
      ∫ q : ℝ, star (φ q) •
        (U (Multiplicative.ofAdd q) : H →L[ℂ] H) (f (r + q)) := by
  rw [regularGaugedPacket_adjoint_apply]
  apply integral_congr_ae
  filter_upwards [regularTranslateApply_ae r f] with q hq
  rw [hq, add_comm q r]

private theorem action_coefficient_integral
    (q u : ℝ) (A : H →L[ℂ] H) (f g : RegularCoreHilbert H) :
    inner ℂ ((regularCoreAction U (Multiplicative.ofAdd q) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)
      (regularConstantHom (volume : Measure ℝ) A
        ((regularCoreAction U (Multiplicative.ofAdd u) :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) g)) =
      ∫ r : ℝ, inner ℂ ((U (Multiplicative.ofAdd q) : H →L[ℂ] H) (f (r + q)))
        (A ((U (Multiplicative.ofAdd u) : H →L[ℂ] H) (g (r + u)))) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [regularCoreAction_apply_ae U (Multiplicative.ofAdd q) f,
    regularCoreAction_apply_ae U (Multiplicative.ofAdd u) g,
    regularConstantHom_apply_ae volume A
      ((regularCoreAction U (Multiplicative.ofAdd u) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) g)] with r hq hu hA
  rw [hq, hA, hu]
  rfl

/-- Haar averaging a packet operator is exactly the constructed
convolution with the same commutant coefficient. -/
theorem integral_packet_orbit_inner_eq
    (φ ψ : Lp ℂ 2 (volume : Measure ℝ))
    (hφ : Integrable φ volume) (hψ : Integrable ψ volume)
    (A : H →L[ℂ] H) (f g : RegularCoreHilbert H) :
    (∫ r : ℝ, inner ℂ
      ((regularGaugedPacket U hU φ).adjoint (regularTranslateApply r f))
      (A ((regularGaugedPacket U hU ψ).adjoint (regularTranslateApply r g)))) =
      inner ℂ f (regularPacketConvolution U hU φ ψ hφ hψ A g) := by
  let K : (ℝ × ℝ) × ℝ → ℂ := fun p =>
    (φ p.1.1 * star (ψ p.1.2)) *
      inner ℂ ((U (Multiplicative.ofAdd p.1.1) : H →L[ℂ] H) (f (p.2 + p.1.1)))
        (A ((U (Multiplicative.ofAdd p.1.2) : H →L[ℂ] H) (g (p.2 + p.1.2))))
  have hK : Integrable K (((volume : Measure ℝ).prod volume).prod volume) :=
    integrable_regularPacket_kernel U hU φ ψ hφ hψ A f g
  have havg : (∫ r : ℝ, inner ℂ
      ((regularGaugedPacket U hU φ).adjoint (regularTranslateApply r f))
      (A ((regularGaugedPacket U hU ψ).adjoint (regularTranslateApply r g)))) =
      ∫ r : ℝ, ∫ p : ℝ × ℝ, K (p, r) ∂((volume : Measure ℝ).prod volume) := by
    apply integral_congr_ae
    filter_upwards [hK.prod_left_ae] with r hr
    rw [packet_adjoint_translate, packet_adjoint_translate,
      inner_integrals _ _ (integrable_packet_translate U hU φ f r)
        (integrable_packet_translate U hU ψ g r) A,
      integral_prod _ hr]
    apply integral_congr_ae
    filter_upwards [] with q
    apply integral_congr_ae
    filter_upwards [] with u
    dsimp only [K]
    simp only [inner_smul_left, map_smul, inner_smul_right, starRingEnd_apply, star_star]
    ring
  rw [havg, ← integral_integral_swap hK]
  rw [integral_prod _ hK.integral_prod_left, inner_regularPacketConvolution]
  apply integral_congr_ae
  filter_upwards [] with q
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [action_coefficient_integral, ← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with r
  dsimp only [K]
  ring

end

end KadisonKastler

end OAI
