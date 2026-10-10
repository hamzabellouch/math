import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.PhysicalFrameSymbols
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.SampledPhysicalFrame
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.PhysicalModulationParameters
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.FixedCutoffProfileIdentity
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffSymbolSampling

namespace OAI

/-! # The actual physical frame controls the sampled modulation tangent -/

open scoped SchwartzMap ContDiff
namespace DefocusingNLS
local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}
local notation "Params" => ProfileSymmetryParameters

variable (a b k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
  (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
  (F : Params →L[ℝ] HomogeneousY a k)
  (hphys : ∀ p y, homogeneousPhysicalCLM a k ha ha1 hk (F p) y =
    (p.1 : ℂ) * (Complex.I * Q y) +
    (p.2.2 : ℂ) * (((a : ℂ) - Complex.I * (b : ℂ)) * Q y + cartesianTransport Q y) +
    cartesianDerivative p.2.1 Q y)

include hphys hQ

theorem physicalFrame_smooth (p : Params) :
    ContDiff ℝ ∞ (fun y => homogeneousPhysicalCLM a k ha ha1 hk (F p) y) := by
  have he : (fun y => homogeneousPhysicalCLM a k ha ha1 hk (F p) y) =
      (fun y => (p.1 : ℂ) * (Complex.I * Q y) +
        (p.2.2 : ℂ) * (((a : ℂ) - Complex.I * (b : ℂ)) * Q y + cartesianTransport Q y) +
        cartesianDerivative p.2.1 Q y) := funext (hphys p)
  rw [he]
  exact ((contDiff_const.mul (contDiff_const.mul hQ)).add
    (contDiff_const.mul ((contDiff_const.mul hQ).add
      (cartesianTransport_contDiff Q hQ)))).add (cartesianDerivative_contDiff Q hQ _)

omit hQ in
theorem physicalFrame_sample_bounded (hS : HasCartesianSymbol (-2 * a) Q)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (hχzero : ∀ y : E, 1 ≤ ‖y‖ → χ y = 0)
    (hF : ∀ p, ContDiff ℝ ∞ (fun y => homogeneousPhysicalCLM a k ha ha1 hk (F p) y)) :
    ∀ p, ∃ B : ℝ, 0 ≤ B ∧ ∀ L : Radius,
      ‖sampledPhysicalFrame a k ha ha1 hk χ hχ F hF L p‖ ≤ B := by
  intro p
  have hs : HasCartesianSymbol (-2 * a)
      (fun y => homogeneousPhysicalCLM a k ha ha1 hk (F p) y) := by
    have he := funext (hphys p)
    rw [he]
    exact physical_symmetry_frame_symbol a b ha hS p
  obtain ⟨B, hB, hb⟩ := cutoffProfile_sampling_of_global_symbol a k ha ha1 hk χ hχ hχzero
    _ (hF p) (hs.global_profile_bound a ha)
  exact ⟨B, hB, fun L => hb L.1 L.2⟩

theorem sampledPhysicalFrame_modulation_tangent
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (hF : ∀ p, ContDiff ℝ ∞ (fun y => homogeneousPhysicalCLM a k ha ha1 hk (F p) y))
    (L : Radius) (p : Params) :
    sampledPhysicalFrame a k ha ha1 hk χ hχ F hF L (physicalModulationParameterEquiv b p) =
      ((a * p.2.2 : ℝ) - (p.1 : ℂ) * Complex.I) •
        fixedCutoffProfile a k ha ha1 hk L χ hχ Q hQ L.1 +
      p.2.2 • fixedCutoffProfile a k ha ha1 hk L χ hχ (cartesianTransport Q)
        (cartesianTransport_contDiff Q hQ) L.1 +
      fixedCutoffProfile a k ha ha1 hk L χ hχ (cartesianDerivative p.2.1 Q)
        (cartesianDerivative_contDiff Q hQ p.2.1) L.1 := by
  have he :
      cutoffProfileSchwartz L.1 (by linarith [L.2]) χ hχ
        (fun y => homogeneousPhysicalCLM a k ha ha1 hk (F (physicalModulationParameterEquiv b p)) y)
        (hF _) =
      ((a * p.2.2 : ℝ) - (p.1 : ℂ) * Complex.I) •
        cutoffProfileSchwartz L.1 (by linarith [L.2]) χ hχ Q hQ +
      p.2.2 • cutoffProfileSchwartz L.1 (by linarith [L.2]) χ hχ (cartesianTransport Q)
        (cartesianTransport_contDiff Q hQ) +
      cutoffProfileSchwartz L.1 (by linarith [L.2]) χ hχ (cartesianDerivative p.2.1 Q)
        (cartesianDerivative_contDiff Q hQ p.2.1) := by
    ext y
    simp only [cutoffProfileSchwartz_apply, add_apply, smul_apply, Complex.real_smul,
      hphys, physicalModulationParameterEquiv_apply]
    push_cast
    ring
  have hs := congrArg (physicalSchwartzTorusSamplingCLM a k L.1 ha1 hk L.2) he
  simpa only [sampledPhysicalFrame_apply, map_add, map_smul, RingHom.id_apply,
    ContinuousLinearMap.map_smul_of_tower, fixedCutoffProfile_self] using hs

end DefocusingNLS

end OAI
