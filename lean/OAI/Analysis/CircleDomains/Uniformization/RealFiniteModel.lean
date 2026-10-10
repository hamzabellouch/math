import OAI.Analysis.CircleDomains.Topology.FiniteJordanModelInput
import OAI.Analysis.CircleDomains.Uniformization.FiniteModelCoordinates
import OAI.Analysis.CircleDomains.Transfer.TransportedRealCoordinates

namespace OAI

/-!
# Principally normalized finite models with real coordinates

The actual real fillings remain real functions after composition with the
smooth inverse of the normalized model. This specialization is used for
the barrier coordinates, whose values zero and one must be retained.
-/

open Set Filter Function MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem finite_metric_model_with_real_fillings
    (hcompact : SmoothCompactMetricSphereUniformization) (hfinite : FiniteJordanModelUniformization)
    {I : Type*} [Finite I] (T : I → ℂ ≃ₜ ℂ)
    (hdisj : Pairwise (Disjoint on fun i => closure (jordanInterior (T i))))
    {K Ω : Set (ℝ × ℝ)} (hKQ : sphericalCore K ⊆ openCompletedRegion T)
    (hQΩ : realChartDomain (completedRegion T) ⊆ Ω)
    (g : (ℝ × ℝ) → PlanarMetric) (hg : ContDiff ℝ ∞ g) (hPD : ∀ z, (g z).PosDef)
    (hfar : ∃ R : ℝ, 0 < R ∧ ∀ z ∉ Metric.closedBall 0 R, g z = sphericalMetricFactor z • 1)
    (hcore : ∀ᶠ z in 𝓝ˢ K, g z = sphericalMetricFactor z • 1)
    {J : Type*} {n : ℕ} {D : J → Set (ℝ × ℝ)}
    {v F : Fin n → (ℝ × ℝ) → ℝ}
    (hF : IsFilledCoordinateFamily D Ω v F) :
    ∃ (V : Set Sphere) (f fi : Sphere → Sphere), IsCircleDomain V ∧
      IsSmoothSphereEquivalence f fi (openCompletedRegion T) V ∧
      IsConformalOn f (sphericalCore K) ∧ IsPrincipalNormalized f ∧
      (∀ l, ContDiffOn ℝ ∞ (F l ∘ sphereRealMap fi) (realChartDomain V) ∧
        ∀ x ∈ realChartDomain (openCompletedRegion T),
          ((F l ∘ sphereRealMap fi) ∘ sphereRealMap f) =ᶠ[𝓝 x] F l) ∧
      (∀ l (s : Set (ℝ × ℝ)), MeasurableSet s → s ⊆ realChartDomain (openCompletedRegion T) →
        (∫ y in sphereRealMap f '' s,
          gradientEnergy (F l ∘ sphereRealMap fi) (fun _ => 1) y) =
          ∫ x in s, gradientEnergy (F l) g x) ∧
      (∀ p ∈ openCompletedRegion T, IsMetricConformalAt g f p) := by
  obtain ⟨V, f, fi, hV, heq, hconf, hmetric, hnorm⟩ :=
    principal_finite_metric_circle_model hcompact hfinite T hdisj hKQ g hg hPD hfar hcore
  have hinf := hKQ (infty_mem_sphericalCore K)
  have hO : IsOpen (realChartDomain (openCompletedRegion T)) :=
    isOpen_realChartDomain (isOpen_openCompletedRegion T)
  have hFO (l : Fin n) : ContDiffOn ℝ ∞ (F l) (realChartDomain (openCompletedRegion T)) :=
    (hF.1 l).mono (fun _ hx => hQΩ (openCompletedRegion_subset_completedRegion T hx))
  have himage : sphereRealMap f '' realChartDomain (openCompletedRegion T) =
      realChartDomain V := (heq.real_bijOn hinf hnorm.1).image_eq
  refine ⟨V, f, fi, hV, heq, hconf, hnorm, ?_, ?_, hmetric⟩
  · intro l
    obtain ⟨_, hsmooth, hpull⟩ := transported_real_coordinate heq hV.1 hinf hnorm.1
      hO (Subset.refl _) (F l) (hFO l)
    exact ⟨himage ▸ hsmooth, hpull⟩
  · intro l s hs hsO
    exact integral_transported_real_coordinate heq hV.1 hinf hnorm.1 hO (Subset.refl _)
      (F l) (hFO l) hs hsO hmetric (fun x _ => hPD x)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
