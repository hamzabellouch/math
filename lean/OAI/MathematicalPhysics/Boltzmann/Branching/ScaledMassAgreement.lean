import OAI.MathematicalPhysics.Boltzmann.Approximation.MildDensityAgreement
import OAI.MathematicalPhysics.Boltzmann.Compactness.KineticDilationIntegral
import OAI.MathematicalPhysics.Boltzmann.Branching.SeparationBoxContainment

namespace OAI

/-! # Passing equality of cap limits to fixed rescaled box masses -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CapLocalLimit.scaled_mass_congr {s₀ η K α γ d₀ q r : ℝ}
    {A : TightCapFamily s₀ η K α γ d₀ q} (L : CapLocalLimit A)
    {g : (ℝ × Position) × Velocity → ℝ} (hg : Measurable g)
    (he : L.density =ᵐ[(AnnularEnvelope.timePositionVolume A.time).prod volume] g)
    (hr : 0 < r) (j : ℕ)
    (hc : kineticDilation r⁻¹ ⁻¹' separationBox j ⊆ TorusKineticChart.region A.time) :
    scaledBoxMass r (TorusKineticChart.liftDensity L.density) j =
      scaledBoxMass r (TorusKineticChart.liftDensity g) j := by
  have hm := fun n => (A.approximation (L.subsequence n)).solution.measurable_value
  have hw₁ := TorusKineticChart.weak_density_transfer hm L.weak_limit
  have hw₂ := TorusKineticChart.weak_density_transfer hm (L.weak_limit.congr_limit hg he)
  exact tendsto_nhds_unique
    (weak_scaled_setIntegral hr (measurableSet_separationBox j) hc hw₁)
    (weak_scaled_setIntegral hr (measurableSet_separationBox j) hc hw₂)

theorem DormantLimit.scaled_mass_tendsto {s₀ η K α γ d₀ q : ℝ}
    {A : DormantFamily s₀ η K α γ d₀ q} (D : DormantLimit A)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : 0 ≤ q) (hqmax : q < 2)
    {r : ℕ → ℝ} (hr : ∀ n, 0 < r n) (hlim : Tendsto r atTop (𝓝 0)) (j : ℕ) :
    Tendsto (fun n => scaledBoxMass (r n) (TorusKineticChart.liftDensity D.density) j)
      atTop (𝓝 0) := by
  have hl := D.scaled_box_L1_tendsto hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
    hsmall hq hqmax (by positivity : 0 < 1/((j:ℝ)+1)) (by norm_num : (0:ℝ) ≤ 1)
    (by positivity : (0:ℝ) ≤ (j:ℝ)+1) hr hlim
  apply squeeze_zero_norm' _ hl
  exact Filter.Eventually.of_forall (fun n => by
    simpa only [scaledBoxMass,separationBox,Real.norm_eq_abs] using
      (norm_integral_le_integral_norm (μ := volume.restrict (separationBox j))
        (fun z => (r n)⁻¹*TorusKineticChart.liftDensity D.density (kineticDilation (r n) z))))

end BoltzmannNonuniqueness.JetCopyDatum

end

end OAI
