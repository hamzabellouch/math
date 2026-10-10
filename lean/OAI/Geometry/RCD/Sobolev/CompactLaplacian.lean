import OAI.Analysis.RCDHeat.ExistingAnalytic

namespace OAI

/-!
# Zero total mass of a compactly supported weak Laplacian

A radial Sobolev cutoff supplies the test function equal to one on both
supports. Locality makes its energy pairing vanish. No constant global
Sobolev function or finiteness of the ambient measure is needed.
-/

open Set MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
  (hQ : QuadraticCheegerEnergy μ)

/-- The integral of a weak Laplacian vanishes when the function and source
are both supported in a fixed ball. -/
theorem integral_weakLaplacian_eq_zero (u : SobolevSpace μ hQ) (q : Lp ℝ 2 μ)
    (hd : IsWeakLaplacian μ hQ u q) (p : X) {R : ℝ} (hR : 0 < R)
    (hu : ∀ᵐ x ∂μ, R < dist p x → SobolevSpace.toLp μ hQ u x = 0)
    (hq : ∀ᵐ x ∂μ, R < dist p x → q x = 0) :
    ∫ x, q x ∂μ = 0 := by
  let η := radialSobolevCutoff μ hQ p hR
  have hη : SobolevSpace.toLp μ hQ η =ᵐ[μ] radialCutoff p R :=
    radialSobolevCutoff_coe μ hQ p hR
  have hgamma : localGamma μ hQ u η =ᵐ[μ] fun _ => 0 := by
    filter_upwards [localGamma_zero_on_level μ hQ u η 0,
      localGamma_zero_on_level μ hQ η u 1, localGamma_comm μ hQ u η,
      hη, hu] with x hzu hzη hc he hx
    by_cases hin : dist p x ≤ R
    · exact hc.trans (hzη (he.trans (radialCutoff_eq_one p hR hin)))
    · exact hzu (hx (lt_of_not_ge hin))
  have henergy : energyForm μ hQ u η = 0 := by
    rw [← integral_localGamma_eq_energyForm]
    exact (integral_congr_ae hgamma).trans (by simp)
  have hinner : ⟪q, SobolevSpace.toLp μ hQ η⟫_ℝ = ∫ x, q x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hη, hq] with x he hx
    by_cases hin : dist p x ≤ R
    · rw [he, radialCutoff_eq_one p hR hin]
      simp
    · rw [hx (lt_of_not_ge hin)]
      simp
  have he := hd η
  rw [henergy, hinner] at he
  linarith

end RegularPointCoordinates

end

end OAI
