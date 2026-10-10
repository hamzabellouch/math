import OAI.Geometry.SurfaceImmersion.Primitive.IndependentCircularCurves
import OAI.Geometry.SurfaceImmersion.Geometry.CompactLeadingRegularity
import OAI.Geometry.SurfaceImmersion.Primitive.ExactCircularPrimitive
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseMetricRegularity
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseMetricRead
import OAI.Geometry.SurfaceImmersion.Primitive.PhaseCircularPeriod
import OAI.Geometry.SurfaceImmersion.Primitive.ExactPhaseOriginalProfiles
import OAI.Geometry.SurfaceImmersion.Primitive.PhaseLeadingProfileStability
import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveProfileStability
import OAI.Geometry.SurfaceImmersion.Geometry.ExactGeometricFastFamily
import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveMetric
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasMetricJetMargins

namespace OAI

/-! Actual finite-accuracy primitive immersions with a Riemannian target,
uniform first-jet bounds, and a uniform nonzero second-form margin. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes CovarianceCorrector GeometryPreservation
local instance independent_exactCircularBoundaryFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance independent_exactCircularBoundaryFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance independent_exactCircularBoundaryDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance independent_exactCircularBoundaryDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance independent_exactCircularBoundarySectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance independent_exactCircularBoundarySectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace MetricGoodPhaseData
open SurfaceJetCoordinates SurfaceVelocityFamily VelocityFrame
variable {g : SmoothMetric M} {F : M → Space}

theorem independent_exact_circular_primitive_boundary [T2Space M] (data : MetricGoodPhaseData g F) (A₀ : SmoothingAtlas M)
    (houter : ∀ i x, x ∈ tsupport (A₀.weight i) → A₀.outer i =ᶠ[𝓝 x] (fun _ => 1))
    (hF : ContMDiff planeModel spaceModel ∞ F) (hmetric : g.inner = inducedTensor F)
    (i : A₀.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {χ : JetPolynomial.Base → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ e.source)
    (hcover : (A₀.chartWeightCompact i : Set JetPolynomial.Base) ⊆ e.source)
    {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)
    {a : SmallModes.Base → ℝ} (ha : ContDiff ℝ ∞ a) (hamp : l.HasSpatialAmplitude (a ∘ baseEquiv))
    {Z : TopologicalSpace.Opens GeometricJet} (hOZ : (O : Set LowJet) ⊆ jetDomain Z)
    {e₁ e₂ : GeometricJet → NormalFrame.Vec}
    (h₁ : ContDiffOn ℝ ∞ e₁ Z) (h₂ : ContDiffOn ℝ ∞ e₂ Z)
    {α : GeometricJet × ℝ → ℝ} (hα : ContDiffOn ℝ ∞ α (Z ×ˢ univ))
    (hvel : ∀ J ∈ O, ∀ t, l.velocity (J,t) =
      velocityRadius (normal J) (a (decode J).1) •
        VelocityFrame.direction (e₁ (decode J)) (e₂ (decode J)) (α (decode J,t)))
    (S : TopologicalSpace.Opens JetPolynomial.Base)
    (hSc : IsCompact (closure (S : Set JetPolynomial.Base))) (hTS : MapsTo e e.source S)
    {Q : Set LowJet} (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (hFQ : MapsTo (lowJet (A₀.jetChartMap i F ∘ e.symm)) S Q)
    (K : Set JetPolynomial.Base) (hK : IsCompact K) (hKS : K ⊆ S)
    (hKA : e.symm '' K ⊆ (A₀.chartWeightCompact i : Set JetPolynomial.Base))
    (hone : ∀ x ∈ e.symm '' K, χ x = 1)
    (hv : ∀ J ∈ O, lowJetPosition J ∉ K → ∀ t, l.velocity (J,t) = SurfaceVelocityFamily.normal J)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ)
    (hℓx : ℓ (coordinateVector 0) = 1) (hℓy : ℓ (coordinateVector 1) = 0)

    (h : SmoothMetric M)
    (htarget : h.inner = g.inner + A₀.bundleRestore A₀.tensorTriv i
      (fun y => fiberFromThree (localizedTensorPullback e χ (fun q => ![(a (baseEquiv q))^2,0,0]) y)))
    {C : Set JetPolynomial.Base} (hC : IsCompact C)
    (hCS : C ⊆ (S : Set JetPolynomial.Base) ∩ e.target)
    {ι : Type*} {Curves : ι → Set SmallModes.Base} {b c k : ι → SmallModes.Base → ℝ}
    (hCurveC : ∀ j x, x ∈ Curves j → baseEquiv.symm x ∈ C)
    (hactive : ∀ j x, x ∈ Curves j → A₀.chartWeight i (e.symm (baseEquiv.symm x)) ≠ 0)
    (hcurv : ∀ j x, x ∈ Curves j → k j x ≤
      RealModes.coordinateGauss (fun y => A₀.phaseMetricRead i e.symm h y 0)
        (fun y => A₀.phaseMetricRead i e.symm h y 1)
        (fun y => A₀.phaseMetricRead i e.symm h y 2) x)
    (η : ℝ) (hη : 0 < η)
    (havoid : ∀ z : ℝ, 0 < z → z < η → ∀ j x, x ∈ Curves j →
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ G : RField 4, ContDiff ℝ ∞ G → ∀ p : SmallModes.Base,
      ‖realBoundaryProfile G z p-surfaceCircularProfile (A₀.phaseRealChartMap i e.symm F)
        a e₁ e₂ α (x,t)‖ < η →
      k j x ≤ RealModes.coordinateGauss (RealModes.realMetric G SmallModes.dx SmallModes.dx)
        (RealModes.realMetric G SmallModes.dx SmallModes.dy) (RealModes.realMetric G SmallModes.dy SmallModes.dy) p →
      RealModes.realSecondForm G (b j x,c j x) (b j x,c j x) p ≠ 0 ∧
      VelocityFrame.normalize (RealModes.realSecondForm G (b j x,c j x) (b j x,c j x) p) ≠
        -profilePreferred (realBoundaryProfile G z p))
    {E : Set SmallModes.Base}
    (hEC : ∀ x ∈ E, baseEquiv.symm x ∈ C)
    (hactiveE : ∀ x ∈ E, A₀.chartWeight i (e.symm (baseEquiv.symm x)) ≠ 0)
    (hdetE : ∀ x ∈ E, A₀.phaseMetricRead i e.symm h x 0 * A₀.phaseMetricRead i e.symm h x 2 -
      (A₀.phaseMetricRead i e.symm h x 1)^2 ≠ 0)
    (B slopeBound : ℝ)
    (hcurvE : ∀ x ∈ E, -B ≤ RealModes.coordinateGauss
      (fun y => A₀.phaseMetricRead i e.symm h y 0)
      (fun y => A₀.phaseMetricRead i e.symm h y 1)
      (fun y => A₀.phaseMetricRead i e.symm h y 2) x)
    (hcross : ∀ z : ℝ, 0 < z → z < η → ∀ x ∈ E, ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ G : RField 4, ContDiff ℝ ∞ G → ∀ p : SmallModes.Base,
      ‖realBoundaryProfile G z p-surfaceCircularProfile (A₀.phaseRealChartMap i e.symm F)
        a e₁ e₂ α (x,t)‖ < η → ∀ κ : ℝ,
      RealModes.coordinateGauss (RealModes.realMetric G SmallModes.dx SmallModes.dx)
        (RealModes.realMetric G SmallModes.dx SmallModes.dy) (RealModes.realMetric G SmallModes.dy SmallModes.dy) p =
        κ*NormalFrame.gramDet (SmallModes.coordDeriv SmallModes.dx G p) (SmallModes.coordDeriv SmallModes.dy G p) →
      -B ≤ RealModes.coordinateGauss (RealModes.realMetric G SmallModes.dx SmallModes.dx)
        (RealModes.realMetric G SmallModes.dx SmallModes.dy) (RealModes.realMetric G SmallModes.dy SmallModes.dy) p →
      ∀ r s : ℝ, |r| ≤ slopeBound → |s| ≤ slopeBound →
        0 < orderedCrossing G (1,r) (1,s) p κ ∧ 0 < orderedCrossing G (1,s) (1,r) p κ ∧
        ((0 < RealModes.realSecondForm G (1,r) (1,r) p ⬝ᵥ profilePreferred (realBoundaryProfile G z p) ∧
          0 < RealModes.realSecondForm G (1,s) (1,s) p ⬝ᵥ profilePreferred (realBoundaryProfile G z p)) ∨
         (0 < RealModes.realSecondForm G (1,r) (1,r) p ⬝ᵥ RealModes.realSecondForm G (1,s) (1,s) p ∧
          ∃ w : NormalFrame.Vec, profilePreferred (realBoundaryProfile G z p) ⬝ᵥ w = 0 ∧
            0 < RealModes.realSecondForm G (1,r) (1,r) p ⬝ᵥ w ∧
            0 < RealModes.realSecondForm G (1,s) (1,s) p ⬝ᵥ w)))
    (hregular : ∀ p ∈ C, ∀ t ∈ Icc (0 : ℝ) 1,
      surfaceCircularProfile (A₀.phaseRealChartMap i e.symm F) a e₁ e₂ α (baseEquiv p,t) ∈
        regularBoundaryProfiles) :
    ∀ ε : ℝ, 0 < ε → ∀ ζ : ℝ, 0 < ζ →
    ∃ z : ℝ, 0 < z ∧ z < ζ ∧ z ≤ 1 ∧ ∃ W : M → Space,
      IsSmoothIsometricImmersion M h W ∧ Nonempty (MetricGoodPhaseData h W) ∧
      (∀ p ∈ C, realBoundaryProfile (A₀.phaseRealChartMap i e.symm W) z (baseEquiv p) ∈
        regularBoundaryProfiles) ∧
      (∀ j x, x ∈ Curves j →
        RealModes.realSecondForm (A₀.phaseRealChartMap i e.symm W) (b j x,c j x) (b j x,c j x) x ≠ 0 ∧
        VelocityFrame.normalize (RealModes.realSecondForm (A₀.phaseRealChartMap i e.symm W)
          (b j x,c j x) (b j x,c j x) x) ≠
          -profilePreferred (realBoundaryProfile (A₀.phaseRealChartMap i e.symm W) z x)) ∧
      (∀ x ∈ E, ∀ r s : ℝ, |r| ≤ slopeBound → |s| ≤ slopeBound →
        let H := A₀.phaseRealChartMap i e.symm W
        let κ := RealModes.coordinateGaussianCurvature
          (RealModes.realMetric H SmallModes.dx SmallModes.dx)
          (RealModes.realMetric H SmallModes.dx SmallModes.dy)
          (RealModes.realMetric H SmallModes.dy SmallModes.dy) x
        0 < orderedCrossing H (1,r) (1,s) x κ ∧ 0 < orderedCrossing H (1,s) (1,r) x κ ∧
        ((0 < RealModes.realSecondForm H (1,r) (1,r) x ⬝ᵥ profilePreferred (realBoundaryProfile H z x) ∧
          0 < RealModes.realSecondForm H (1,s) (1,s) x ⬝ᵥ profilePreferred (realBoundaryProfile H z x)) ∨
         (0 < RealModes.realSecondForm H (1,r) (1,r) x ⬝ᵥ RealModes.realSecondForm H (1,s) (1,s) x ∧
          ∃ w : NormalFrame.Vec, profilePreferred (realBoundaryProfile H z x) ⬝ᵥ w = 0 ∧
            0 < RealModes.realSecondForm H (1,r) (1,r) x ⬝ᵥ w ∧
            0 < RealModes.realSecondForm H (1,s) (1,s) x ⬝ᵥ w))) ∧
      ∃ G : M → Space, ∃ _hG : ContMDiff planeModel spaceModel ∞ G,
        A₀.WeightedBound 1 3 ε (G-F) ∧
        ∃ V : M → Space, ContMDiff planeModel spaceModel ∞ V ∧
          A₀.WeightedBound 1 2 (z^8) (W-V) ∧
          (∀ p ∉ tsupport (A₀.weight i), V =ᶠ[𝓝 p] G) ∧
        ∀ p ∉ A₀.phaseSurfaceSupport i e K, V =ᶠ[𝓝 p] G := by
  intro ε hε ζ hζ
  let hGO : MapsTo (lowJet (A₀.jetChartMap i F ∘ e.symm)) S O := fun _ hp => hQO (hFQ hp)
  have hreg : ∀ p ∈ C, ∀ t ∈ Icc (0 : ℝ) 1,
      boundaryProfileMap (l.geometricLeadingProfile (A₀.jetChartMap i F ∘ e.symm)
        ((A₀.jetChartMap_smooth i hF).comp hi) hGO p (t : Period)) ∈ regularBoundaryProfiles := by
    intro p hp t ht
    rw [A₀.phase_circular_geometric_profile i hF hi ha hOZ l hamp h₁ h₂ hα hvel hGO (hCS hp).1 t]
    exact hregular p hp t ht
  obtain ⟨δreg,hδreg,hnearreg⟩ := l.compact_leading_regularity
    ((A₀.jetChartMap_smooth i hF).comp hi) hGO hC (fun p hp => (hCS hp).1) hreg
  let δ := min ε (min η δreg)
  have hδ : 0 < δ := lt_min hε (lt_min hη hδreg)
  have hδη : δ ≤ η := (min_le_right _ _).trans (min_le_left _ _)
  have hδr : δ ≤ δreg := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨z,hz,hzζ,hz1,W,hW,hgeometry,hprofiles,G,hG,hslow,V,hV,hcorrection,hext⟩ :=
    data.independent_exact_circular_primitive_profiles A₀ houter hF hmetric i e he hi hχ hχc hχs hcover
      l ha hamp hOZ h₁ h₂ hα hvel S hSc hTS hQ hQO hFQ K hK hKS hKA hone hv ℓ hℓx hℓy
      h htarget hC hCS δ hδ (min ζ η) (lt_min hζ hη)
  refine ⟨z,hz,hzζ.trans_le (min_le_left _ _),hz1,W,hW,hgeometry,?_,?_,?_,G,hG,?_,V,hV,hcorrection,hext⟩
  · intro p hp
    obtain ⟨t,ht,herror⟩ := hprofiles p hp
    have heq := A₀.phase_circular_geometric_profile i hF hi ha hOZ l hamp h₁ h₂ hα hvel hGO (hCS hp).1 t
    rw [← heq] at herror
    exact hnearreg p hp t ht _ (herror.trans_le hδr)
  · intro j x hx
    obtain ⟨t,ht,herror⟩ := hprofiles (baseEquiv.symm x) (hCurveC j x hx)
    rw [baseEquiv.apply_symm_apply] at herror
    apply havoid z hz (hzζ.trans_le (min_le_right _ _)) j x hx t ht
      (A₀.phaseRealChartMap i e.symm W) (A₀.phaseRealChartMap_smooth i hi hW.1) x
      (herror.trans_le hδη)
    rw [A₀.phaseGauss_isometry i hi hW (hactive j x hx)]
    exact hcurv j x hx
  · intro x hx r s hr hs
    obtain ⟨t,ht,herror⟩ := hprofiles (baseEquiv.symm x) (hEC x hx)
    rw [baseEquiv.apply_symm_apply] at herror
    let H := A₀.phaseRealChartMap i e.symm W
    have hDH : NormalFrame.gramDet (SmallModes.coordDeriv SmallModes.dx H x)
        (SmallModes.coordDeriv SmallModes.dy H x) ≠ 0 := by
      rw [A₀.phaseMetricRead_isometry_det i hi hW (hactiveE x hx)]
      exact hdetE x hx
    apply hcross z hz (hzζ.trans_le (min_le_right _ _)) x hx t ht H
      (A₀.phaseRealChartMap_smooth i hi hW.1) x (herror.trans_le hδη)
      _ (RealModes.coordinateGauss_eq_curvature_mul H x hDH) _ r s hr hs
    rw [A₀.phaseGauss_isometry i hi hW (hactiveE x hx)]
    exact hcurvE x hx
  · exact fun j => (hslow j).mono_const (min_le_left _ _)

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
