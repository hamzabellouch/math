import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralL2Multiplier

namespace OAI

/-! Complex linearity of bounded real multiplication, used to preserve the smooth-jet closure. -/

open MeasureTheory
namespace DefocusingNLS

noncomputable def spectralL2ComplexMultiplier (μ : Measure ℝ) (q : ℝ → ℝ)
    (hq : AEStronglyMeasurable q μ) (M : ℝ) (hb : ∀ᵐ r ∂μ, ‖q r‖ ≤ M) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  let A := spectralL2Weight μ q hq M hb
  let L : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ :=
    { toFun := A
      map_add' := by
        intro u v
        exact (spectralL2Multiplier μ q hq M hb).map_add u v
      map_smul' := by
        intro c u
        apply Lp.ext
        filter_upwards [spectralL2Weight_ae μ q hq M hb (c • u),
          spectralL2Weight_ae μ q hq M hb u,Lp.coeFn_smul c u,Lp.coeFn_smul c (A u)]
          with r hcu hu hin hout
        change A (c • u) r=(c • A u : Lp ℂ 2 μ) r
        rw [hcu,hout,hin,Pi.smul_apply,Pi.smul_apply,hu]
        exact smul_comm (q r) c (u r) }
  L.mkContinuous M (fun u => spectralL2Weight_norm μ q hq M hb u)

theorem spectralL2ComplexMultiplier_ae (μ : Measure ℝ) (q : ℝ → ℝ)
    (hq : AEStronglyMeasurable q μ) (M : ℝ) (hb : ∀ᵐ r ∂μ, ‖q r‖ ≤ M) (u : Lp ℂ 2 μ) :
    spectralL2ComplexMultiplier μ q hq M hb u =ᵐ[μ] fun r => q r • u r :=
  spectralL2Weight_ae μ q hq M hb u

theorem spectralL2ComplexMultiplier_norm (μ : Measure ℝ) (q : ℝ → ℝ)
    (hq : AEStronglyMeasurable q μ) (M : ℝ) (hb : ∀ᵐ r ∂μ, ‖q r‖ ≤ M) (u : Lp ℂ 2 μ) :
    ‖spectralL2ComplexMultiplier μ q hq M hb u‖ ≤ M*‖u‖ :=
  spectralL2Weight_norm μ q hq M hb u

end DefocusingNLS

end OAI
