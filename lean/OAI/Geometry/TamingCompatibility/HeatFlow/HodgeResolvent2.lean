import Mathlib
import OAI.Geometry.TamingCompatibility.HeatFlow.HodgeActualResolvent
import OAI.Geometry.TamingCompatibility.Hodge.HodgeUnitDual

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set MeasureTheory
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
lemma same_resolvent_current_kernel (n : ℕ) :
    let := geometricMetricSpace J α hs ht
    ∃ T L Q : ℝ, ∃ hT : 0 < T, T ≤ 1 ∧
      VolterraKernel.HeatBound (geometricVolume A J α) n T L (globalLeading J α ht A E) ∧
      VolterraKernel.HeatBound (geometricVolume A J α) n T Q (globalCorrection J α ht A E T) ∧
      (∀ r : ℝ, 0 < r →
        Continuous (fun p : X × X => HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r p.1 p.2) ∧
        Continuous (fun p : X × X => HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r p.1 p.2)) ∧
      (∀ r : ℝ, 0 < r → ∀ x y : X,
        VolterraBounds.weight n (r^2) x y *
          ‖HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r x y‖ ≤
            ((1/120:ℝ)*L*2^(n-1)*(HodgeKernelBounds.moment 3 1+HodgeKernelBounds.moment (3+n) 1))/r^4 ∧
        VolterraBounds.weight n (r^2) x y *
          ‖HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r x y‖ ≤
            ((1/120:ℝ)*(4*L*Q)*2^(n-1)*(HodgeKernelBounds.moment 4 1+HodgeKernelBounds.moment (4+n) 1))/r^2) ∧
      ∀ (r : ℝ) (hr : 0 < r) (C : HodgeSmoothingCover A J α hs ht D hD r hr)
        (ρ : ℝ) (hρ : 0 < ρ) (B : HodgeSmoothingCover A J α hs ht D hD ρ hρ),
        2*ρ^2 ≤ T → ∀ g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type),
        ∀ u v : MetricUnit g,
        C.innerKernel g u v =
          framePairing A J α ht E (unitDual A J α hs ht E hE g u).val u.val.proj
            ((HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r u.val.proj v.val.proj +
              HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r u.val.proj v.val.proj)
                (frameEncode J α ht A E v.val.proj ((unitDual A J α hs ht E hE g v).val v.val.proj))) +
          B.gammaTailKernel g T hT.le r u v := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  obtain ⟨T,L,Q,hT,hT1,hL,hQ,hcont,hbound,hgram⟩ :=
    same_resolvent_actual_gram A J α hs ht E hE D hD n
  refine ⟨T,L,Q,hT,hT1,hL,hQ,hcont,hbound,?_⟩
  intro r hr C ρ hρ B hρT g u v
  have h := hgram r hr C ρ hρ B hρT
    (unitDual A J α hs ht E hE g v) (unitDual A J α hs ht E hE g u) u.val.proj v.val.proj
  rw [pairingEvaluationVector_unitDual C u,pairingEvaluationVector_unitDual C v,
    pairingGammaTail_unitDual B T hT.le r u v] at h
  exact h

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
