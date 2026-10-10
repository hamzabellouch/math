import OAI.NumberTheory.DirichletL.Moments.Fourier

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentPoisson
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson CubicEisenstein
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentSupportedCorrelation
open CenteredMomentFourier

theorem full_gauss_pair_poisson (u v : O) (hu : u ≠ 0) (hv : v ≠ 0)
    (χu : MulChar (Residue u) ℂ) (χv : MulChar (Residue v) ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    letI := finite_quotient_span hu
    letI := finite_quotient_span hv
    letI : Fintype (Residue u) := Fintype.ofFinite _
    letI : Fintype (Residue v) := Fintype.ofFinite _
    (∑' z : O, residueGauss u hu χu (Ideal.Quotient.mk _ z) *
      star (residueGauss v hv χv (Ideal.Quotient.mk _ z)) * W (‖eisEmbedding z‖ ^ 2 / K)) =
      (K : ℂ) * ∑' j : O, fullModulusCorrelation u v χu χv (-j) *
        paperRadialFourier W (K * ‖eisEmbedding j‖ ^ 2 / ‖eisEmbedding (u * v)‖ ^ 2) := by
  let := finite_quotient_span hu
  let := finite_quotient_span hv
  let := finite_quotient_span (mul_ne_zero hu hv)
  let : Fintype (Residue u) := Fintype.ofFinite _
  let : Fintype (Residue v) := Fintype.ofFinite _
  let : Fintype (Residue (u * v)) := Fintype.ofFinite _
  let P := fun h : Residue (u * v) =>
    residueGauss u hu χu (frequencyReduction u (u * v) (dvd_mul_right u v) h) *
      star (residueGauss v hv χv (frequencyReduction v (u * v) (dvd_mul_left v u) h))
  have hcoeff (j : O) :
      (∑ r : Residue (u * v), P r * quotientTrace (u * v) (mul_ne_zero hu hv)
        (Ideal.Quotient.mk _ j * r)) =
      (Fintype.card (Residue (u * v)) : ℂ) * fullModulusCorrelation u v χu χv (-j) := by
    have ht := actual_gauss_correlation u v hu hv χu χv (-j)
    have heq (r : Residue (u * v)) : -(r * Ideal.Quotient.mk _ (-j)) =
        Ideal.Quotient.mk _ j * r := by
      simp only [map_neg, mul_neg, neg_neg]
      exact mul_comm _ _
    simp_rw [heq] at ht
    exact ht
  have hcard : (Fintype.card (Residue (u * v)) : ℂ) = (‖eisEmbedding (u * v)‖ ^ 2 : ℝ) := by
    rw [eisEmbedding_norm_sq_eq_absNorm_span, Ideal.absNorm_apply,
      Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    norm_cast
  have hpoisson := actual_radial_paper_poisson_trace W K hK (u * v) (mul_ne_zero hu hv) P
  change (∑' z : O, P (Ideal.Quotient.mk _ z) * W (‖eisEmbedding z‖ ^ 2 / K)) =
    (K / ‖eisEmbedding (u * v)‖ ^ 2 : ℝ) •
      ∑' j : O, (∑ r : Residue (u * v), P r * quotientTrace (u * v) (mul_ne_zero hu hv)
        (Ideal.Quotient.mk _ j * r)) *
          paperRadialFourier W (K * ‖eisEmbedding j‖ ^ 2 / ‖eisEmbedding (u * v)‖ ^ 2) at hpoisson
  simp only [P, frequencyReduction_mk] at hpoisson ⊢
  rw [hpoisson]
  change (K / ‖eisEmbedding (u * v)‖ ^ 2 : ℝ) •
    (∑' j : O, (∑ r : Residue (u * v), P r * quotientTrace (u * v) (mul_ne_zero hu hv)
      (Ideal.Quotient.mk _ j * r)) *
      paperRadialFourier W (K * ‖eisEmbedding j‖ ^ 2 / ‖eisEmbedding (u * v)‖ ^ 2)) = _
  simp_rw [hcoeff, hcard, mul_assoc]
  rw [tsum_mul_left, Complex.real_smul, Complex.ofReal_div, ← mul_assoc]
  have hn : (‖eisEmbedding (u * v)‖ ^ 2 : ℂ) ≠ 0 := by
    exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr
      (eisEmbedding_ne_zero (mul_ne_zero hu hv))))
  rw [Complex.ofReal_pow, div_mul_cancel₀ _ hn]

theorem normalized_gauss_pair_poisson (u v : O) (hu : u ≠ 0) (hv : v ≠ 0)
    (χu : MulChar (Residue u) ℂ) (χv : MulChar (Residue v) ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    letI := finite_quotient_span hu
    letI := finite_quotient_span hv
    letI : Fintype (Residue u) := Fintype.ofFinite _
    letI : Fintype (Residue v) := Fintype.ofFinite _
    (∑' z : O, normalizedResidueGauss u hu χu (Ideal.Quotient.mk _ z) *
      star (normalizedResidueGauss v hv χv (Ideal.Quotient.mk _ z)) * W (‖eisEmbedding z‖ ^ 2 / K)) =
      ((K : ℂ) / ((Real.sqrt (Ideal.absNorm (Ideal.span {u}) : ℝ) : ℂ) *
        (Real.sqrt (Ideal.absNorm (Ideal.span {v}) : ℝ) : ℂ))) *
      ∑' j : O, fullModulusCorrelation u v χu χv (-j) *
        paperRadialFourier W (K * ‖eisEmbedding j‖ ^ 2 / ‖eisEmbedding (u * v)‖ ^ 2) := by
  let := finite_quotient_span hu
  let := finite_quotient_span hv
  let : Fintype (Residue u) := Fintype.ofFinite _
  let : Fintype (Residue v) := Fintype.ofFinite _
  let ru : ℂ := Real.sqrt (Ideal.absNorm (Ideal.span {u}) : ℝ)
  let rv : ℂ := Real.sqrt (Ideal.absNorm (Ideal.span {v}) : ℝ)
  have hterm (z : O) :
      normalizedResidueGauss u hu χu (Ideal.Quotient.mk _ z) *
        star (normalizedResidueGauss v hv χv (Ideal.Quotient.mk _ z)) * W (‖eisEmbedding z‖ ^ 2 / K) =
      (ru * rv)⁻¹ * (residueGauss u hu χu (Ideal.Quotient.mk _ z) *
        star (residueGauss v hv χv (Ideal.Quotient.mk _ z)) * W (‖eisEmbedding z‖ ^ 2 / K)) := by
    simp only [normalizedResidueGauss, star_div₀, Complex.star_def, Complex.conj_ofReal]
    dsimp only [ru, rv]
    ring
  simp_rw [hterm]
  rw [tsum_mul_left, full_gauss_pair_poisson u v hu hv χu χv W K hK]
  dsimp only [ru, rv]
  ring

theorem sextic_gauss_pair_poisson (u v : O)
    (hu : CanonicalQuadraticSieve.Supported (Ideal.span {u}))
    (hv : CanonicalQuadraticSieve.Supported (Ideal.span {v}))
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    (∑' z : O,
      (ProbePhysical.sexticGauss u (supported_element_ne_zero u hu) z /
        (Real.sqrt (Ideal.absNorm (Ideal.span {u}) : ℝ) : ℂ)) *
      star (ProbePhysical.sexticGauss v (supported_element_ne_zero v hv) z /
        (Real.sqrt (Ideal.absNorm (Ideal.span {v}) : ℝ) : ℂ)) * W (‖eisEmbedding z‖ ^ 2 / K)) =
      ((K : ℂ) / ((Real.sqrt (Ideal.absNorm (Ideal.span {u}) : ℝ) : ℂ) *
        (Real.sqrt (Ideal.absNorm (Ideal.span {v}) : ℝ) : ℂ))) *
      ∑' j : O, actualCorrelation u v hu hv (-j) *
        paperRadialFourier W (K * ‖eisEmbedding j‖ ^ 2 / ‖eisEmbedding (u * v)‖ ^ 2) := by
  have h := normalized_gauss_pair_poisson u v
    (supported_element_ne_zero u hu) (supported_element_ne_zero v hv)
    (supportedModulusCharacter u hu) (supportedModulusCharacter v hv) W K hK
  simpa only [normalizedResidueGauss, residueGauss_supported_mk, actualCorrelation,
    supportedCorrelation] using h

end SevenEighths.CenteredMomentPoisson
end

end OAI
