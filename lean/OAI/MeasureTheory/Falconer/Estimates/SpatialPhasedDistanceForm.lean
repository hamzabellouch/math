import OAI.MeasureTheory.Falconer.Fourier.SpatialPhasedSymbols
import OAI.MeasureTheory.Falconer.Fourier.DistanceKernelSplitting

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter

 theorem spatialPhasedDistanceF_formula (s : ℝ) (ξ : Plane)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (X Y : Set Plane) (M₁ M₂ : ℝ) (ψ : UnitCircle → ℂ)
    (b₁ b₂ : Plane → UnitCircle → ℂ) (hψ : Measurable ψ)
    (h₁ : Measurable (fun z : Plane × UnitCircle => b₁ z.1 z.2))
    (h₂ : Measurable (fun z : Plane × UnitCircle => b₂ z.1 z.2))
    {P B₁ B₂ : ℝ} (hP : 0 ≤ P) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hp : ∀ ω, ‖ψ ω‖ ≤ P) (hb₁ : ∀ x ω, ‖b₁ x ω‖ ≤ B₁)
    (hb₂ : ∀ y ω, ‖b₂ y ω‖ ≤ B₂) (r : ℝ) :
    sourceDistanceF ψ
      (fun z => sourceAngularTransform ρ X M₁ (spatialPhasedSymbol s ξ b₁) z.1 z.2)
      (fun z => sourceAngularTransform ν Y M₂ (spatialPhasedSymbol s ξ b₂) z.1 z.2) r =
      (M₁*M₂)⁻¹ • (∫ z, spatialPairPhase s ξ z * sourceDistanceKernel ψ b₁ b₂ r z.1 z.2
        ∂((ρ.restrict X).prod (ν.restrict Y))) := by
  have hm₁ := spatialPhasedSymbol_measurable s ξ b₁ h₁
  have hm₂ := spatialPhasedSymbol_measurable s ξ b₂ h₂
  have hb₁' : ∀ x ω, ‖spatialPhasedSymbol s ξ b₁ x ω‖ ≤ B₁ := by
    intro x ω; rw [spatialPhasedSymbol_norm]; exact hb₁ x ω
  have hb₂' : ∀ x ω, ‖spatialPhasedSymbol s ξ b₂ x ω‖ ≤ B₂ := by
    intro x ω; rw [spatialPhasedSymbol_norm]; exact hb₂ x ω
  rw [sourceDistanceF_endpoint_integral ρ ν X Y M₁ M₂ ψ _ _ hψ hm₁ hm₂
    hP hB₁ hB₂ hp hb₁' hb₂']
  have hm : Measurable (fun z : Plane × Plane => sourceDistanceKernel ψ
      (spatialPhasedSymbol s ξ b₁) (spatialPhasedSymbol s ξ b₂) r z.1 z.2) :=
    (measurable_sourceDistanceKernel ψ _ _ hψ hm₁ hm₂).comp (f := fun z : Plane × Plane => (r,z))
      (show Measurable (fun z : Plane × Plane => (r,z)) from measurable_const.prodMk measurable_id)
  have hi : Integrable (fun z : Plane × Plane => sourceDistanceKernel ψ
      (spatialPhasedSymbol s ξ b₁) (spatialPhasedSymbol s ξ b₂) r z.1 z.2)
      ((ρ.restrict X).prod (ν.restrict Y)) :=
    Integrable.of_bound hm.aestronglyMeasurable (P*B₁*B₂*sourceArcLength.real univ)
      (Eventually.of_forall (fun z => sourceDistanceKernel_norm_le ψ _ _ hP hB₁ hB₂
        hp hb₁' hb₂' r z.1 z.2))
  rw [← integral_prod _ hi]
  simp_rw [sourceDistanceKernel_phased]

 theorem spatialPhasedDistanceF_joint_measurable (s : ℝ)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (X Y : Set Plane) (M₁ M₂ : ℝ) (ψ : UnitCircle → ℂ)
    (b₁ b₂ : Plane → UnitCircle → ℂ) (hψ : Measurable ψ)
    (h₁ : Measurable (fun z : Plane × UnitCircle => b₁ z.1 z.2))
    (h₂ : Measurable (fun z : Plane × UnitCircle => b₂ z.1 z.2))
    {P B₁ B₂ : ℝ} (hP : 0 ≤ P) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hp : ∀ ω, ‖ψ ω‖ ≤ P) (hb₁ : ∀ x ω, ‖b₁ x ω‖ ≤ B₁)
    (hb₂ : ∀ y ω, ‖b₂ y ω‖ ≤ B₂) :
    Measurable (fun p : Plane × ℝ => sourceDistanceF ψ
      (fun z => sourceAngularTransform ρ X M₁ (spatialPhasedSymbol s p.1 b₁) z.1 z.2)
      (fun z => sourceAngularTransform ν Y M₂ (spatialPhasedSymbol s p.1 b₂) z.1 z.2) p.2) := by
  simp_rw [spatialPhasedDistanceF_formula s _ ρ ν X Y M₁ M₂ ψ b₁ b₂ hψ h₁ h₂
    hP hB₁ hB₂ hp hb₁ hb₂]
  have hphase : Measurable (fun p : (Plane × ℝ) × (Plane × Plane) =>
      spatialPairPhase s p.1.1 p.2) :=
    (spatialPairPhase_continuous s).measurable.comp (f := fun p : (Plane × ℝ) × (Plane × Plane) => (p.1.1,p.2))
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hkernel : Measurable (fun p : (Plane × ℝ) × (Plane × Plane) =>
      sourceDistanceKernel ψ b₁ b₂ p.1.2 p.2.1 p.2.2) :=
    (measurable_sourceDistanceKernel ψ b₁ b₂ hψ h₁ h₂).comp (f := fun p : (Plane × ℝ) × (Plane × Plane) => (p.1.2,p.2))
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hm : Measurable (fun p : Plane × ℝ =>
      ∫ z, spatialPairPhase s p.1 z * sourceDistanceKernel ψ b₁ b₂ p.2 z.1 z.2
        ∂((ρ.restrict X).prod (ν.restrict Y))) :=
    (hphase.mul hkernel).stronglyMeasurable.integral_prod_right'.measurable
  exact hm.const_smul ((M₁*M₂)⁻¹ : ℝ)

end PlanarFalconer

end OAI
