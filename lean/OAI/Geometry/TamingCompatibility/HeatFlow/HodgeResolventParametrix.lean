import Mathlib
import OAI.Geometry.TamingCompatibility.HeatFlow.HodgeHeatWeight
import OAI.Geometry.TamingCompatibility.Hodge.HodgeGammaSplit

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter MeasureTheory
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
lemma same_resolvent_parametrix (n : ℕ) :
    let := geometricMetricSpace J α hs ht
    ∃ T L C : ℝ, 0 < T ∧ T ≤ 1 ∧
      VolterraKernel.HeatBound (geometricVolume A J α) n T L (globalLeading J α ht A E) ∧
      VolterraKernel.HeatBound (geometricVolume A J α) n T C (globalCorrection J α ht A E T) ∧
      ∀ v : X → FrameSpace A, Continuous v →
      ∃ f : L2 A J α hs ht true,
        (∀ a : PreL2 A J α hs ht true,
          ⟪f,smoothL2 A J α hs ht true a⟫ =
            ∫ y, framePairing A J α ht E a.val y (v y) ∂geometricVolume A J α) ∧
        (∀ r : ℝ, 0 < r → ∀ a : PreL2 A J α hs ht true,
          ⟪(hodgeRegularization A J α hs ht r ^ 2) f,smoothL2 A J α hs ht true a⟫ =
            (1/120 : ℝ) * (∫ s : ℝ in Ioc 0 (T/r^2), hodgeGammaWeight s *
              (kernelWeakAction A J α ht E (globalLeading J α ht A E) v a.val (r^2*s) +
               kernelWeakAction A J α ht E (globalError J α ht A E T) v a.val (r^2*s))) +
            ⟪hodgeGammaTailAction A J α hs ht D hD T r f,smoothL2 A J α hs ht true a⟫) ∧
        (∀ N : ℕ, ∀ r : ℝ, 0 < r →
          ‖hodgeGammaTailAction A J α hs ht D hD T r f‖ ≤
            ((1/120 : ℝ) * HodgeKernelBounds.moment 5 (1/2) * (N.factorial : ℝ) * (2/T)^N) *
              r^(2*N)*‖f‖) := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  obtain ⟨T,L,C,hT,hT1,hL,hC,hheat⟩ := globalCandidate_eq_spectral A J α hs ht E hE D hD n
  refine ⟨T,L,C,hT,hT1,hL,hC,?_⟩
  intro v hv
  obtain ⟨f,hf,hpair⟩ := hheat v hv
  refine ⟨f,hf,?_,fun N r hr => hodgeGammaTailAction_rapid A J α hs ht D hD N hT hr f⟩
  intro r hr a
  rw [hodgeRegularization_gamma_test_split A J α hs ht D hD hT.le hr]
  congr 2
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hsp
  have hsq : 0 < r^2 := sq_pos_of_pos hr
  have hst : r^2*s ∈ Ioc 0 T := ⟨mul_pos hsq hsp.1,by
    have hh := (le_div_iff₀ hsq).mp hsp.2
    simpa only [mul_comm] using hh⟩
  rw [hpair a _ hst]

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
