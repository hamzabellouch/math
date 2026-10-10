import OAI.Analysis.CircleDomains.Topology.FiniteJordanModelInput
import OAI.Analysis.CircleDomains.Uniformization.RealFiniteModel

namespace OAI

/-! The same principal model transports both the real barriers and the
masked circle coordinates, with exact energy identities for each. -/

open Set Filter Function MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

theorem finite_metric_model_with_mixed_fillings
    (hcompact : SmoothCompactMetricSphereUniformization) (hfinite : FiniteJordanModelUniformization)
    {I : Type*} [Finite I] (T : I → ℂ ≃ₜ ℂ)
    (hdisj : Pairwise (Disjoint on fun i => closure (jordanInterior (T i))))
    {K Ω : Set (ℝ × ℝ)} (hKQ : sphericalCore K ⊆ openCompletedRegion T)
    (hQΩ : realChartDomain (completedRegion T) ⊆ Ω)
    (g : (ℝ × ℝ) → PlanarMetric) (hg : ContDiff ℝ ∞ g) (hPD : ∀ z, (g z).PosDef)
    (hfar : ∃ R : ℝ, 0 < R ∧ ∀ z ∉ Metric.closedBall 0 R, g z = sphericalMetricFactor z • 1)
    (hcore : ∀ᶠ z in 𝓝ˢ K, g z = sphericalMetricFactor z • 1)
    {J : Type*} {n : ℕ} {D : J → Set (ℝ × ℝ)} {M : Fin n → Set (ℝ × ℝ)}
    {v F : Fin n → (ℝ × ℝ) → UnitAddCircle}
    (hF : IsMaskedFilledCircleFamily D Ω M v F)
    {R : Type*} (W : R → (ℝ × ℝ) → ℝ)
    (hW : ∀ j, ContDiffOn ℝ ∞ (W j) Ω) :
    ∃ (V : Set Sphere) (f fi : Sphere → Sphere), IsCircleDomain V ∧
      IsSmoothSphereEquivalence f fi (openCompletedRegion T) V ∧
      IsConformalOn f (sphericalCore K) ∧ IsPrincipalNormalized f ∧
      (∀ l, IsOpen (sphereRealMap f '' (realChartDomain (openCompletedRegion T) ∩ interior (M l))) ∧
        SmoothCircleOn (F l ∘ sphereRealMap fi)
          (sphereRealMap f '' (realChartDomain (openCompletedRegion T) ∩ interior (M l))) ∧
        (∀ x ∈ realChartDomain (openCompletedRegion T) ∩ interior (M l),
          ((F l ∘ sphereRealMap fi) ∘ sphereRealMap f) =ᶠ[𝓝 x] F l)) ∧
      (∀ l (s : Set (ℝ × ℝ)), MeasurableSet s →
        s ⊆ realChartDomain (openCompletedRegion T) ∩ interior (M l) →
        (∫ y in sphereRealMap f '' s,
          fieldEnergy (circleGradient (F l ∘ sphereRealMap fi)) (fun _ => 1) y) =
        ∫ x in s, fieldEnergy (circleGradient (F l)) g x) ∧
      (∀ j, ContDiffOn ℝ ∞ (W j ∘ sphereRealMap fi) (realChartDomain V) ∧
        ∀ x ∈ realChartDomain (openCompletedRegion T),
          ((W j ∘ sphereRealMap fi) ∘ sphereRealMap f) =ᶠ[𝓝 x] W j) ∧
      (∀ j (s : Set (ℝ × ℝ)), MeasurableSet s → s ⊆ realChartDomain (openCompletedRegion T) →
        (∫ y in sphereRealMap f '' s, gradientEnergy (W j ∘ sphereRealMap fi) (fun _ => 1) y) =
          ∫ x in s, gradientEnergy (W j) g x) ∧
      (∀ p ∈ openCompletedRegion T, IsMetricConformalAt g f p) := by
  obtain ⟨V, f, fi, hV, heq, hconf, hmetric, hnorm⟩ :=
    principal_finite_metric_circle_model hcompact hfinite T hdisj hKQ g hg hPD hfar hcore
  have hinf := hKQ (infty_mem_sphericalCore K)
  have hO : IsOpen (realChartDomain (openCompletedRegion T)) :=
    isOpen_realChartDomain (isOpen_openCompletedRegion T)
  have hFO (l : Fin n) : SmoothCircleOn (F l)
      (realChartDomain (openCompletedRegion T) ∩ interior (M l)) := by
    intro x hx
    exact hF.1 l x ⟨hQΩ (openCompletedRegion_subset_completedRegion T hx.1), hx.2⟩
  have hWO (j : R) : ContDiffOn ℝ ∞ (W j) (realChartDomain (openCompletedRegion T)) :=
    (hW j).mono (fun _ hx => hQΩ (openCompletedRegion_subset_completedRegion T hx))
  have himage : sphereRealMap f '' realChartDomain (openCompletedRegion T) =
      realChartDomain V := (heq.real_bijOn hinf hnorm.1).image_eq
  refine ⟨V, f, fi, hV, heq, hconf, hnorm, ?_, ?_, ?_, ?_, hmetric⟩
  · intro l
    exact transported_circle_coordinate heq hV.1 hinf hnorm.1
      (hO.inter isOpen_interior) inter_subset_left (F l) (hFO l)
  · intro l s hs hsO
    exact integral_transported_circle_coordinate heq hV.1 hinf hnorm.1
      (hO.inter isOpen_interior) inter_subset_left (F l) (hFO l) hs hsO
      hmetric (fun x _ => hPD x)
  · intro j
    obtain ⟨_, hsmooth, hpull⟩ := transported_real_coordinate heq hV.1 hinf hnorm.1
      hO (Subset.refl _) (W j) (hWO j)
    exact ⟨himage ▸ hsmooth, hpull⟩
  · intro j s hs hsO
    exact integral_transported_real_coordinate heq hV.1 hinf hnorm.1 hO (Subset.refl _)
      (W j) (hWO j) hs hsO hmetric (fun x _ => hPD x)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
