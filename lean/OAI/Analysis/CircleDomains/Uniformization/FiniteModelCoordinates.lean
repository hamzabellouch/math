import OAI.Analysis.CircleDomains.Topology.FiniteJordanModelInput
import OAI.Analysis.CircleDomains.Uniformization.PrincipalFiniteModel
import OAI.Analysis.CircleDomains.Topology.TransportedCircleCoordinates
import OAI.Analysis.CircleDomains.Rigidity.MaskedCircleFillings

namespace OAI

/-!
# Coordinates on the actual finite circle model

The circle domain, its smooth inverse and the target coordinates are
constructed from the finite metric completion. Every measurable piece
of a source mask has exactly the same Dirichlet energy on its image.
-/

open Set Filter Function MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem openCompletedRegion_subset_completedRegion {I : Type*} (T : I → ℂ ≃ₜ ℂ) :
    openCompletedRegion T ⊆ completedRegion T := by
  intro p hp hbad
  obtain ⟨i, z, hz, rfl⟩ := mem_iUnion.mp hbad
  exact hp (mem_iUnion.mpr ⟨i, z, subset_closure hz, rfl⟩)

theorem finite_metric_model_with_coordinates
    (hcompact : SmoothCompactMetricSphereUniformization) (hfinite : FiniteJordanModelUniformization)
    {I : Type*} [Finite I] (T : I → ℂ ≃ₜ ℂ)
    (hdisj : Pairwise (Disjoint on fun i => closure (jordanInterior (T i))))
    {K : Set (ℝ × ℝ)} (hKQ : sphericalCore K ⊆ openCompletedRegion T)
    (g : (ℝ × ℝ) → PlanarMetric) (hg : ContDiff ℝ ∞ g) (hPD : ∀ z, (g z).PosDef)
    (hfar : ∃ R : ℝ, 0 < R ∧ ∀ z ∉ Metric.closedBall 0 R, g z = sphericalMetricFactor z • 1)
    (hcore : ∀ᶠ z in 𝓝ˢ K, g z = sphericalMetricFactor z • 1)
    {n : ℕ} (O : Fin n → Set (ℝ × ℝ)) (hO : ∀ l, IsOpen (O l))
    (hOU : ∀ l, O l ⊆ realChartDomain (openCompletedRegion T))
    (F : Fin n → (ℝ × ℝ) → UnitAddCircle) (hF : ∀ l, SmoothCircleOn (F l) (O l)) :
    ∃ (V : Set Sphere) (f fi : Sphere → Sphere), IsCircleDomain V ∧
      IsSmoothSphereEquivalence f fi (openCompletedRegion T) V ∧
      IsConformalOn f (sphericalCore K) ∧ IsPrincipalNormalized f ∧
      (∀ l, IsOpen (sphereRealMap f '' O l) ∧
        SmoothCircleOn (F l ∘ sphereRealMap fi) (sphereRealMap f '' O l) ∧
        (∀ x ∈ O l, ((F l ∘ sphereRealMap fi) ∘ sphereRealMap f) =ᶠ[𝓝 x] F l)) ∧
      (∀ l (s : Set (ℝ × ℝ)), MeasurableSet s → s ⊆ O l →
        (∫ y in sphereRealMap f '' s,
          fieldEnergy (circleGradient (F l ∘ sphereRealMap fi)) (fun _ => 1) y) =
        ∫ x in s, fieldEnergy (circleGradient (F l)) g x) := by
  obtain ⟨V, f, fi, hV, hequiv, hconf, hmetric, hnorm⟩ :=
    principal_finite_metric_circle_model hcompact hfinite T hdisj hKQ
      g hg hPD hfar hcore
  have hinf := hKQ (infty_mem_sphericalCore K)
  have hfix := hnorm.1
  refine ⟨V, f, fi, hV, hequiv, hconf, hnorm, ?_, ?_⟩
  · intro l
    exact transported_circle_coordinate hequiv hV.1 hinf hfix (hO l) (hOU l) (F l) (hF l)
  · intro l s hs hsO
    exact integral_transported_circle_coordinate hequiv hV.1 hinf hfix
      (hO l) (hOU l) (F l) (hF l) hs hsO hmetric (fun x _ => hPD x)

/-- The source regions are the actual mask interiors of the completion.
No extra source coordinates or smoothness assumptions are introduced. -/
theorem finite_metric_model_with_masked_fillings
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
    (hF : IsMaskedFilledCircleFamily D Ω M v F) :
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
        ∫ x in s, fieldEnergy (circleGradient (F l)) g x) := by
  apply finite_metric_model_with_coordinates hcompact hfinite T hdisj hKQ g hg hPD hfar hcore
    (fun l => realChartDomain (openCompletedRegion T) ∩ interior (M l))
    (fun _ => (isOpen_realChartDomain (isOpen_openCompletedRegion T)).inter isOpen_interior)
    (fun _ => inter_subset_left) F
  intro l x hx
  exact hF.1 l x ⟨hQΩ (openCompletedRegion_subset_completedRegion T hx.1), hx.2⟩

end CircleDomainRigidity.FiniteTransfer

end

end OAI
