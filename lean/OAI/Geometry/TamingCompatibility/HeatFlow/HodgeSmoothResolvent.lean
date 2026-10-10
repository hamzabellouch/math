import Mathlib
import OAI.Geometry.TamingCompatibility.HeatFlow.HodgeContinuousResolvent
import OAI.Geometry.TamingCompatibility.Hodge.HodgeSmoothSpatial

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
attribute [local irreducible] framePairing globalLeading globalResidual hodgeLaplacian

include hE D hD in
lemma same_resolvent_smooth_spatial (n : ℕ) :
    let := geometricMetricSpace J α hs ht
    ∃ T L C : ℝ, 0 < T ∧ T ≤ 1 ∧
      VolterraKernel.HeatBound (geometricVolume A J α) n T L (globalLeading J α ht A E) ∧
      VolterraKernel.HeatBound (geometricVolume A J α) n T C (globalCorrection J α ht A E T) ∧
      (∀ r : ℝ, 0 < r →
        Continuous (fun p : X × X => HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r p.1 p.2) ∧
        Continuous (fun p : X × X => HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r p.1 p.2)) ∧
      (∀ r : ℝ, 0 < r → ∀ x y : X,
        VolterraBounds.weight n (r^2) x y *
          ‖HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r x y‖ ≤
            ((1/120:ℝ)*L*2^(n-1)*(HodgeKernelBounds.moment 3 1+HodgeKernelBounds.moment (3+n) 1))/r^4 ∧
        VolterraBounds.weight n (r^2) x y *
          ‖HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r x y‖ ≤
            ((1/120:ℝ)*(4*L*C)*2^(n-1)*(HodgeKernelBounds.moment 4 1+HodgeKernelBounds.moment (4+n) 1))/r^2) ∧
      ∀ b : PreL2 A J α hs ht true,
        ∀ r : ℝ, 0 < r → ∀ a : PreL2 A J α hs ht true,
          ⟪(hodgeRegularization A J α hs ht r ^ 2) (smoothL2 A J α hs ht true b),smoothL2 A J α hs ht true a⟫ =
            (∫ y, ∫ x, framePairing A J α ht E a.val x
              (HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r x y (frameEncode J α ht A E y (b.val y)))
                ∂geometricVolume A J α ∂geometricVolume A J α) +
            (∫ y, ∫ x, framePairing A J α ht E a.val x
              (HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r x y (frameEncode J α ht A E y (b.val y)))
                ∂geometricVolume A J α ∂geometricVolume A J α) +
            ⟪hodgeGammaTailAction A J α hs ht D hD T r (smoothL2 A J α hs ht true b),smoothL2 A J α hs ht true a⟫ := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  obtain ⟨T,L,C,hT,hT1,hL,hC,hcont,hbound,hpair⟩ :=
    same_resolvent_continuous_spatial A J α hs ht E hE D hD n
  refine ⟨T,L,C,hT,hT1,hL,hC,hcont,hbound,?_⟩
  intro b
  obtain ⟨f,hf,hfr⟩ := hpair (fun y => frameEncode J α ht A E y (b.val y))
    (frameEncode_section_smooth J α ht A E hE hs b.val b.property).continuous
  have he := smoothL2_eq_of_framePairings A J α hs ht E hE f b hf
  subst f
  exact hfr

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
