import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFluxSmoothness
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeCoefficientSmoothness

namespace OAI

/-! Local smoothness of the actual flux ODE throughout the free exterior. -/

open Set
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem spectralFluxSolution_contDiffOn (ell : ℕ) (μ A : ℝ → ℝ)
    (c ζ : ℂ) (l R : ℝ) (hl : 0 < l) (U : ℝ → E₄)
    (hμ : ∀ α β : ℝ, l < α → β < R → ContDiffOn ℝ ∞ μ (Icc α β))
    (hA : ∀ α β : ℝ, l < α → β < R → ContDiffOn ℝ ∞ A (Icc α β))
    (hpos : ∀ r ∈ Ioo l R, μ r ≠ 0)
    (hU : ∀ r ∈ Ioo l R, HasDerivAt U (spectralFluxField ell (μ r) (A r) c ζ r (U r)) r) :
    ContDiffOn ℝ ∞ U (Ioo l R) := by
  intro r hr
  let α := (l+r)/2
  let β := (r+R)/2
  have hα : l < α := by dsimp [α]; linarith [hr.1]
  have hβ : β < R := by dsimp [β]; linarith [hr.2]
  have har : α < r := by dsimp [α]; linarith [hr.1]
  have hrb : r < β := by dsimp [β]; linarith [hr.2]
  have hs : Icc α β ⊆ Ioo l R := fun x hx => ⟨hα.trans_le hx.1,hx.2.trans_lt hβ⟩
  have hc : ContDiffOn ℝ ∞ U (Icc α β) := by
    apply ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt
      (f := fun x V => spectralFluxField ell (μ x) (A x) c ζ x V)
      (u := (univ : Set E₄))
    · exact spectralFluxField_contDiffOn ell μ A c ζ (Icc α β)
        (hμ α β hα hβ) (hA α β hα hβ)
        (fun x hx => hpos x (hs hx)) (fun x hx => (hl.trans (hs hx).1).ne')
    · exact fun x hx => (hU x (hs hx)).hasDerivWithinAt
    · exact fun _ _ => mem_univ _
  exact (hc.contDiffAt (Icc_mem_nhds har hrb)).contDiffWithinAt

theorem radialMatchedFreeFlux_contDiffOn (ell : ℕ) (z : ProfileMatchingBall)
    (hz₁ : z.val.1=0) (hz : diskProfile (profileMatchingParameter z)=0)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (R : ℝ) (ζ : ℂ) (U : ℝ → E₄)
    (hU : ∀ r ∈ Ioo (radialShootingR (profileMatchingParameter z)) R,
      HasDerivAt U (spectralFluxField ell (radialMatchedFreeMassFunction z r)
        (radialMatchedFreeTransportFunction z r) 6 ζ r (U r)) r) :
    ContDiffOn ℝ ∞ U (Ioo (radialShootingR (profileMatchingParameter z)) R) := by
  apply spectralFluxSolution_contDiffOn ell _ _ 6 ζ _ R
    (lt_of_lt_of_le (by norm_num) (radialShooting_geometry (profileMatchingParameter z)).2.1) U
    _ _ _ hU
  · intro α β hα _
    exact (radialMatchedFreeMass_contDiffOn_matched z hz₁ hz).mono
      (fun _ hr => hα.trans_le hr.1)
  · intro α β hα _
    exact radialMatchedFreeTransport_contDiffOn_matched z hz₁ hz hc α β hα
  · intro r hr
    exact (radialMatchedFreeMass_pos z r
      (le_trans (by linarith [(radialShooting_geometry (profileMatchingParameter z)).2.1]) hr.1.le)).ne'

end DefocusingNLS

end OAI
