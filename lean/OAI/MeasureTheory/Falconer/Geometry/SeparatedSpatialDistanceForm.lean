import OAI.MeasureTheory.Falconer.Estimates.SpatialDistanceFormSeparation

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter

 theorem separatedSpatialDistanceForm (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) {s : ℝ} (hs : 0 < s) (ρ ν : Measure Plane)
    [IsFiniteMeasure ρ] [IsFiniteMeasure ν] (X Y : Set Plane)
    (hX : MeasurableSet X) (hY : MeasurableSet Y)
    (hsep : ∀ x ∈ X, ∀ y ∈ Y, δ ≤ dist x y / s ∧ dist x y / s ≤ L)
    (M₁ M₂ : ℝ) (ψ : UnitCircle → ℂ) (b₁ b₂ : Plane → UnitCircle → ℂ)
    (hψ : Measurable ψ)
    (h₁ : Measurable (fun z : Plane × UnitCircle => b₁ z.1 z.2))
    (h₂ : Measurable (fun z : Plane × UnitCircle => b₂ z.1 z.2))
    {P B₁ B₂ : ℝ} (hP : 0 ≤ P) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hp : ∀ ω, ‖ψ ω‖ ≤ P) (hb₁ : ∀ x ω, ‖b₁ x ω‖ ≤ B₁)
    (hb₂ : ∀ y ω, ‖b₂ y ω‖ ≤ B₂) (r : ℝ) :
    (M₁*M₂)⁻¹ • (∫ z, (↑((dist z.1 z.2 / s)^j)⁻¹ : ℂ) *
      sourceDistanceKernel ψ b₁ b₂ r z.1 z.2 ∂((ρ.restrict X).prod (ν.restrict Y))) =
      ∫ ξ, spatialFourierCoeff δ L hδ hL j ξ *
        sourceDistanceF ψ
          (fun z => sourceAngularTransform ρ X M₁ (spatialPhasedSymbol s ξ b₁) z.1 z.2)
          (fun z => sourceAngularTransform ν Y M₂ (spatialPhasedSymbol s ξ b₂) z.1 z.2) r := by
  rw [← spatialDistanceForm_separation δ L hδ hL j s ρ ν X Y M₁ M₂ ψ b₁ b₂
    hψ h₁ h₂ hP hB₁ hB₂ hp hb₁ hb₂]
  congr 1
  apply integral_congr_ae
  have hx : ∀ᵐ z ∂((ρ.restrict X).prod (ν.restrict Y)), z.1 ∈ X :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hX)
  have hy : ∀ᵐ z ∂((ρ.restrict X).prod (ν.restrict Y)), z.2 ∈ Y :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hY)
  filter_upwards [hx,hy] with z hz₁ hz₂
  have hd := hsep z.1 hz₁ z.2 hz₂
  have he := spatialInverseDistance_separation δ L hδ hL j hs hd.1 hd.2
  rw [spatialFourierSeparation] at he
  rw [he]

end PlanarFalconer

end OAI
