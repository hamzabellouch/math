import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarGreenBoundary
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralGreenSmallness

namespace OAI

/-! The scalar boundary representation gives an explicit error estimate
relative to the outgoing extension of the prescribed left value. -/

open Set
namespace DefocusingNLS

theorem spectralScalar_outgoing_extension_error
    (R E r k kap A C M B : ℝ) (hR : 0 < R) (hr : r ∈ Icc R E)
    (hk : 0 ≤ k) (hkap : 0 < kap) (hA : 0 ≤ A) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (D U q : ℝ → ℂ × ℂ) (V f : ℝ → ℂ) (W beta : ℂ)
    (hDc : ContinuousOn D (Icc R E)) (hUc : ContinuousOn U (Icc R E))
    (hqc : ContinuousOn q (Icc R E)) (hfc : ContinuousOn f (Icc R E))
    (hW : W ≠ 0) (hdet : ∀ t ∈ Icc R E, spectralScalarWronskian (D t) (U t) = W)
    (hD : ∀ t ∈ Icc R E, HasDerivAt D (spectralScalarField (V t) (D t)) t)
    (hU : ∀ t ∈ Icc R E, HasDerivAt U (spectralScalarField (V t) (U t)) t)
    (hq : ∀ t ∈ Icc R E, HasDerivAt q (spectralScalarField (V t) (q t)+(0,f t)) t)
    (hDR : (D R).1 = 0) (hUR : (U R).1 ≠ 0) (hUE : (U E).2 = beta*(U E).1)
    (hleft : ∀ t ∈ Icc R r, spectralShellNorm k (((D t).1/W) • U r) ≤ A/kap)
    (hright : ∀ t ∈ Icc r E, spectralShellNorm k (((U t).1/W) • D r) ≤ A/kap)
    (hforcing : ∀ t ∈ Icc R E, ‖f t‖ ≤ C/(kap*t^2)*M)
    (hboundary : ‖(q E).2-beta*(q E).1‖ ≤ B) :
    spectralShellNorm k (q r-((q R).1/(U R).1) • U r) ≤
      A/kap*B+A*C*M/(kap^2*R) := by
  let e := (q E).2-beta*(q E).1
  have he := spectralScalarGreen_boundary_representation R E D U q V f W beta
    hDc hUc hqc hfc hW hdet hD hU hq hDR hUR hUE r hr
  have hrep : q r-((q R).1/(U R).1) • U r =
      e • (((-((U E).1))/W) • D r)+spectralScalarGreenIntegral R E D U W f r := by
    rw [he,smul_smul]
    dsimp only [e]
    rw [mul_comm e]
    abel
  have hrightE := hright E ⟨hr.2,le_rfl⟩
  have hneg : spectralShellNorm k (((-((U E).1))/W) • D r) ≤ A/kap := by
    rw [neg_div,spectralShellNorm_smul,norm_neg]
    simpa only [spectralShellNorm_smul] using hrightE
  have hb : spectralShellNorm k (e • (((-((U E).1))/W) • D r)) ≤ A/kap*B := by
    rw [spectralShellNorm_smul]
    calc
      _ ≤ ‖e‖*(A/kap) := mul_le_mul_of_nonneg_left hneg (norm_nonneg _)
      _ ≤ B*(A/kap) := mul_le_mul_of_nonneg_right hboundary (div_nonneg hA hkap.le)
      _ = _ := mul_comm _ _
  have hg := spectralScalarGreenIntegral_small R E r k kap A C M hR hr hk hkap hA hC hM
    D U W f hDc hUc hfc hleft hright hforcing
  rw [hrep]
  exact (spectralShellNorm_add_le k hk _ _).trans (add_le_add hb hg)

end DefocusingNLS

end OAI
