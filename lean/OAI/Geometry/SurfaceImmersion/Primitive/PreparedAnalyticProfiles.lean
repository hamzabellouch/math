import OAI.Geometry.SurfaceImmersion.Primitive.PreparedCircularDefiners
import OAI.Geometry.SurfaceImmersion.Atlas.IntrinsicPhaseChartGeometry
import OAI.Geometry.SurfaceImmersion.Primitive.ActualAnalyticProfiledLoop

namespace OAI

/-! The supported geometric loop for a genuine centered phase and the
prepared finite family of coordinate circles. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold Matrix
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes RealModes PhaseGeometry SurfaceVelocityFamily VelocityFrame NormalFrame SurfaceJetCoordinates GeometryPreservation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]
variable {ι : Type*} [Fintype ι]

theorem prepared_circular_analytic_profiles
    (q : M) (center : ι → M) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (hreg : ∀ i, circularCoordinateRegion (center i) (r i) ⊆ (coordinateChart (center i)).target)
    (ell : Base) (L R : ℝ) (hpair : (circularCrossingSet center r).Finite)
    (htang : ∀ i, (circularPhaseTangencies q (center i) ell L (r i) R).Finite)
    (e : OpenPartialHomeomorph Base Base) (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    (hdom : e.source ⊆ (coordinateChart q).target)
    (hphase : ∀ x, (e x).1 = centeredConvexPhase ell L (coordinateChart q q) x)
    {F n : Base → Vec} {a : Base → ℝ}
    (hF : ContDiff ℝ ∞ F) (ha : ContDiff ℝ ∞ a) (hn : ContDiffOn ℝ ∞ n e.source)
    (hI : ∀ x ∈ e.source, Function.Injective (fderiv ℝ F x))
    (hN : ∀ x ∈ e.source, (∀ v, fderiv ℝ F x v ⬝ᵥ n x = 0) ∧ n x ⬝ᵥ n x = 1)
    (hHess : ∀ x ∈ e.source, ∀ v : Base, v ≠ 0 →
      0 < coordinateMetricHessian (inducedCoordinateMetric F)
        (centeredConvexPhase ell L (coordinateChart q q)) x v v)
    {T K : Set Base} (hT : IsCompact T) (hTe : T ⊆ e.target)
    (haT : ∀ p ∈ T, 0 ≤ a p)
    (hboundary : ∀ p ∈ T, a p = 0 → ∀ v : Base, v ≠ 0 →
      realSecondForm F v v (e.symm p) ≠ 0 ∧
      normalize (realSecondForm F v v (e.symm p)) ≠ -n (e.symm p))
    (hK : IsCompact K) (hKT : K ⊆ T) (haK : ∀ p ∈ K, 0 < a p)
    (hcover : ∀ x ∈ K, ∃ i, (coordinateChart q).symm (e.symm x) ∈ circularBoundary (center i) (r i))
    (hregion : ∀ x ∈ K, (coordinateChart q).symm (e.symm x) ∈ circularDiskClosure q R)
    :
    ∃ sLo sHi D : ℝ, 0 < sLo ∧ 0 < sHi ∧ 0 ≤ D ∧
    ∀ H : ℝ, 0 ≤ H →
    ∃ Z : TopologicalSpace.Opens GeometricJet, CollarVelocity.jetSection (F ∘ e.symm) '' T ⊆ Z ∧
      ∃ e₁ e₂ : GeometricJet → Vec,
        ContDiffOn ℝ ∞ e₁ Z ∧ ContDiffOn ℝ ∞ e₂ Z ∧
        (∀ j ∈ Z, e₁ j ⬝ᵥ e₁ j = 1 ∧ e₂ j ⬝ᵥ e₂ j = 1 ∧ e₁ j ⬝ᵥ e₂ j = 0 ∧
          j.2 1 ⬝ᵥ e₁ j = 0 ∧ j.2 4 ⬝ᵥ e₁ j = 0 ∧ j.2 1 ⬝ᵥ e₂ j = 0 ∧ j.2 4 ⬝ᵥ e₂ j = 0) ∧
      ∃ O : TopologicalSpace.Opens JetPolynomial.LowJet, (O : Set JetPolynomial.LowJet) ⊆ jetDomain Z ∧
      ∃ l : Loop O,
        IsCompact (JetPolynomial.lowJet ((F ∘ e.symm) ∘ baseEquiv) '' (baseEquiv ⁻¹' T)) ∧
        JetPolynomial.lowJet ((F ∘ e.symm) ∘ baseEquiv) '' (baseEquiv ⁻¹' T) ⊆ O ∧
        l.HasSpatialAmplitude (a ∘ baseEquiv) ∧
        (∀ J ∈ O, a (baseEquiv (JetPolynomial.lowJetPosition J)) = 0 →
          ∀ t, l.velocity (J,t) = normal J) ∧
        ∃ α : GeometricJet × ℝ → ℝ, ContDiffOn ℝ ∞ α (Z ×ˢ univ) ∧
          (∀ j ∈ Z, Function.Periodic (fun t => α (j,t)) 1) ∧
          (∀ J t, l.velocity (J,t) = velocityRadius (normal J) (a (decode J).1) •
            direction (e₁ (decode J)) (e₂ (decode J)) (α (decode J,t))) ∧
          ∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) 1,
            let J := surfaceCircularProfile (F ∘ e.symm) a e₁ e₂ α (x,t)
            J ∈ regularBoundaryProfiles ∧
            sLo ≤ profileCoefficients J 0 ∧ profileCoefficients J 0 ≤ sHi ∧
            |profileCoefficients J 1| ≤ D ∧
            (profileCoefficients J 3 = 0 → H+2 < |profileCoefficients J 2|) := by
  obtain ⟨P,hP,hPK,hlocal⟩ := prepared_circular_definers q center r hr hreg ell L R
    hpair htang e he hi hdom hphase (hKT.trans hTe) hcover hregion
  have hg := inverse_phase_chart_geometry hF
    (centeredConvexPhase_smooth ell L (coordinateChart q q)) e he hi hphase hI hN hHess
  have hn' : ContDiffOn ℝ ∞ (n ∘ e.symm) e.target :=
    hn.comp hi.contDiffOn (fun _ hp => e.map_target hp)
  exact actual_analytic_surface_loop_profiles (hF.comp hi) ha hT e.open_target hTe hn'
    (fun p hp => (hg p hp).1) (fun p hp => (hg p hp).2.1) (fun p hp => (hg p hp).2.2)
    haT (fun p hp hz => inverse_phase_chart_antipode hF e he hi (hTe hp)
      (hI _ (e.map_target (hTe hp))) (hboundary p hp hz))
    hK hKT haK hP hPK hlocal

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
