import OAI.Analysis.CircleDomains.Topology.FiniteJordanModelInput
import OAI.Analysis.CircleDomains.Rigidity.ActualMaskedTransfer
import OAI.Analysis.CircleDomains.Uniformization.FiniteModelCoordinates
import OAI.Analysis.CircleDomains.Transfer.CompletedChart

namespace OAI

/-!
# Principally normalized actual masked finite transfer

The selected cutoff and filled metric produce a normalized finite circle
model with its smooth inverse and actual transported coordinates. The
source energy estimates and exact target energy formula hold for the same
width, metric, model and coordinates.
-/

open Set Filter Function MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem principal_actual_masked_transfer
    (hcompact : SmoothCompactMetricSphereUniformization) (hfinite : FiniteJordanModelUniformization)
    {J : Type*} [Finite J] (T : J → ℂ ≃ₜ ℂ)
    (hTdisj : Pairwise (Disjoint on fun j => closure (jordanInterior (T j))))
    {I : Type*} [Fintype I] {n : ℕ}
    (D : I → Set (ℝ × ℝ)) (hD : ∀ i, IsOpen (D i))
    (hdisj : Pairwise (Disjoint on fun i => closure (D i)))
    (hfrontc : ∀ i, IsCompact (frontier (D i)))
    (hfrontconn : ∀ i, IsConnected (frontier (D i)))
    {G K : Set (ℝ × ℝ)} (hG : IsOpen G)
    (hK : IsClosed K) (hKc : IsCompact (closure Kᶜ)) (hKG : K ⊆ G)
    (hKQ : sphericalCore K ⊆ openCompletedRegion T)
    (hcover : realChartDomain (completedRegion T) ⊆ G ∪ ⋃ i, D i)
    (hKD : ∀ x ∈ K, ∀ i, x ∉ D i)
    (M : Fin n → Set (ℝ × ℝ)) (hM : ∀ i, IsClosed (M i))
    (hboundary : ∀ i, frontier (M i) ⊆ interior K)
    (f : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (hf : ∀ l, SmoothCircleOn (f l) (G ∩ interior (M l)))
    (hf2 : ∀ l, MemLp (circleGradient (f l)) 2 (volume.restrict (G ∩ M l)))
    (χ : (ℝ × ℝ) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχzero : ∀ᶠ x in 𝓝ˢ K, χ x = 0)
    (O : I → Set (ℝ × ℝ)) (hO : ∀ i, IsOpen (O i))
    (hDO : ∀ i, frontier (D i) ⊆ O i)
    (hχone : ∀ i x, x ∈ O i → χ x = 1)
    (u : I → Fin n → (ℝ × ℝ) → ℝ) (hu : ∀ i l, ContDiffOn ℝ ∞ (u i l) (O i))
    (hproj : ∀ i l x, x ∈ O i → (u i l x : UnitAddCircle) = f l x)
    (N : ℕ) (active : I → Fin n) (θ : Fin n → ℝ)
    (havoid : ∀ i l, l ≠ active i →
      Disjoint (u i l '' frontier (D i)) (shiftedLattice (reciprocalGridStep N) (θ l)))
    (hvi : ∀ k, IntegrableOn (maskedCircleWedges M (circleCutoffFamily f χ N
      (staircaseWidth (reciprocalGridStep N) k) θ)) (G \ K))
    {ε : ℝ} (hgood : ∃ᶠ k in atTop, (∫ z in G \ K, maskedCircleWedges M
      (circleCutoffFamily f χ N (staircaseWidth (reciprocalGridStep N) k) θ) z) < ε / 2)
    (k₀ : ℕ) :
    ∃ (k : ℕ) (F : Fin n → (ℝ × ℝ) → UnitAddCircle)
      (R : ℝ) (g : (ℝ × ℝ) → PlanarMetric)
      (V : Set Sphere) (φ φi : Sphere → Sphere),
      k₀ ≤ k ∧ IsMaskedFilledCircleFamily D (G ∪ ⋃ i, D i) M
        (circleCutoffFamily f χ N (staircaseWidth (reciprocalGridStep N) k) θ) F ∧
      (∀ᶠ z in 𝓝ˢ K, ∀ i, F i z = f i z) ∧
      0 < R ∧ ContDiff ℝ ∞ g ∧ (∀ z, (g z).PosDef) ∧
      (∀ᶠ z in 𝓝ˢ K, g z = sphericalMetricFactor z • 1) ∧
      (∀ z ∉ Metric.closedBall 0 R, g z = sphericalMetricFactor z • 1) ∧
      (∑ i : Fin n, ∫ z in (realChartDomain (completedRegion T) \ K) ∩ M i,
        fieldEnergy (circleGradient (F i)) g z) < ε ∧
      (∀ i : Fin n, ∀ E : Set (ℝ × ℝ), MeasurableSet E → E ⊆ K →
        (∫ z in (realChartDomain (completedRegion T) \ E) ∩ M i,
          fieldEnergy (circleGradient (F i)) g z) <
        (∫ z in (G \ E) ∩ M i, fieldEnergy (circleGradient (f i))
          (fun z => sphericalMetricFactor z • 1) z) + ε) ∧
      IsCircleDomain V ∧ IsSmoothSphereEquivalence φ φi (openCompletedRegion T) V ∧
      IsConformalOn φ (sphericalCore K) ∧ IsPrincipalNormalized φ ∧
      (∀ l, IsOpen (sphereRealMap φ '' (realChartDomain (openCompletedRegion T) ∩ interior (M l))) ∧
        SmoothCircleOn (F l ∘ sphereRealMap φi)
          (sphereRealMap φ '' (realChartDomain (openCompletedRegion T) ∩ interior (M l))) ∧
        (∀ x ∈ realChartDomain (openCompletedRegion T) ∩ interior (M l),
          ((F l ∘ sphereRealMap φi) ∘ sphereRealMap φ) =ᶠ[𝓝 x] F l)) ∧
      (∀ l (s : Set (ℝ × ℝ)), MeasurableSet s →
        s ⊆ realChartDomain (openCompletedRegion T) ∩ interior (M l) →
        (∫ y in sphereRealMap φ '' s,
          fieldEnergy (circleGradient (F l ∘ sphereRealMap φi)) (fun _ => 1) y) =
        ∫ x in s, fieldEnergy (circleGradient (F l)) g x) := by
  obtain ⟨k, F, R, g, hlate, hfill, hretain, hR, hg, hPD, hcore, hfar, htail, hlocal⟩ :=
    transfer_actual_masked_circle_cutoff D hD hdisj hfrontc hfrontconn hG
      (isClosed_real_completedRegion T) hK hKc hKG hcover hKD M hM hboundary f hf hf2
      χ hχ hχzero O hO hDO hχone u hu hproj N active θ havoid hvi hgood k₀
  obtain ⟨V, φ, φi, hV, heq, hconf, hnorm, hcoordinates, henergy⟩ :=
    finite_metric_model_with_masked_fillings hcompact hfinite T hTdisj hKQ hcover
      g hg hPD ⟨R, hR, hfar⟩ hcore hfill
  exact ⟨k, F, R, g, V, φ, φi, hlate, hfill, hretain, hR, hg, hPD, hcore, hfar,
    htail, hlocal, hV, heq, hconf, hnorm, hcoordinates, henergy⟩

end CircleDomainRigidity.FiniteTransfer

end

end OAI
