import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeGammaWeakAction

namespace OAI

section

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
lemma same_resolvent_continuous_data (n : ℕ) :
    let := geometricMetricSpace J α hs ht
    ∃ T L C : ℝ, 0 < T ∧ T ≤ 1 ∧
      VolterraKernel.HeatBound (geometricVolume A J α) n T L (globalLeading J α ht A E) ∧
      VolterraKernel.HeatBound (geometricVolume A J α) n T C (globalCorrection J α ht A E T) ∧
      (∀ t ∈ Ioc 0 T, Continuous (fun p : X × X => globalError J α ht A E T t p.1 p.2)) ∧
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
  obtain ⟨T,L,C,hT,hT1,hL,hC,hEc,hheat⟩ := globalCandidate_continuous_eq_spectral A J α hs ht E hE D hD n
  refine ⟨T,L,C,hT,hT1,hL,hC,hEc,?_⟩
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
lemma same_resolvent_continuous_spatial (n : ℕ) :
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
      ∀ v : X → FrameSpace A, Continuous v → ∃ f : L2 A J α hs ht true,
        (∀ a : PreL2 A J α hs ht true,
          ⟪f,smoothL2 A J α hs ht true a⟫ =
            ∫ y, framePairing A J α ht E a.val y (v y) ∂geometricVolume A J α) ∧
        ∀ r : ℝ, 0 < r → ∀ a : PreL2 A J α hs ht true,
          ⟪(hodgeRegularization A J α hs ht r ^ 2) f,smoothL2 A J α hs ht true a⟫ =
            (∫ y, ∫ x, framePairing A J α ht E a.val x
              (HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r x y (v y))
                ∂geometricVolume A J α ∂geometricVolume A J α) +
            (∫ y, ∫ x, framePairing A J α ht E a.val x
              (HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r x y (v y))
                ∂geometricVolume A J α ∂geometricVolume A J α) +
            ⟪hodgeGammaTailAction A J α hs ht D hD T r f,smoothL2 A J α hs ht true a⟫ := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  let := geometricVolume_finite A J α hs ht
  obtain ⟨T,L,C,hT,hT1,hL,hC,hEc,hpair⟩ := same_resolvent_continuous_data A J α hs ht E hE D hD n
  have hL0 := hL.weight_zero (geometricVolume A J α)
  have hC0 := hC.weight_zero (geometricVolume A J α)
  have hErr : VolterraKernel.HeatBound (geometricVolume A J α) 0 T (4*T*L*C)
      (globalError J α ht A E T) := by
    simpa only [globalError] using VolterraKernel.convolution_heatBound (geometricVolume A J α) 0 hT.le _ _ hL0 hC0
  have hEm : VolterraKernel.MeasurableKernel (globalError J α ht A E T) := by
    simpa only [globalError] using VolterraKernel.convolution_measurable (geometricVolume A J α) _ _ hL.measurable hC.measurable
  have hLsup (t : ℝ) (htp : t ∈ Ioc 0 T) (x y : X) :
      ‖globalLeading J α ht A E t x y‖ ≤ L/t^2 := by
    simpa only [VolterraBounds.weight,pow_zero,one_mul] using hL0.sup t htp x y
  have hEsup (t : ℝ) (htp : t ∈ Ioc 0 T) (x y : X) :
      ‖globalError J α ht A E T t x y‖ ≤ (4*L*C)/t^1 := by
    simpa only [globalError,VolterraBounds.weight,pow_zero,one_mul,pow_one] using
      (VolterraKernel.convolution_sup (geometricVolume A J α) 0 _ _ hL0 hC0 htp x y).2
  refine ⟨T,L,C,hT,hT1,hL,hC,?_,?_,?_⟩
  · intro r hr
    refine ⟨globalLeading_gamma_continuous A J α hs ht E hE hr hL0,?_⟩
    exact HodgeKernelBounds.gammaKernel_continuous 4 1 (by norm_num) hr _ hEm hEsup hEc
  · intro r hr x y
    have h := globalGamma_bounds_of A J α hs ht E n hL hC hr x y
    exact ⟨h.1.2,h.2.2⟩
  · intro v hv
    obtain ⟨f,hf,hfr,_htail⟩ := hpair v hv
    refine ⟨f,hf,?_⟩
    intro r hr a
    rw [hfr r hr a,
      gammaKernel_weakAction A J α hs ht E hE 3 2 (by norm_num) hr hL.nonneg _ hL.measurable hLsup v hv a.val a.property,
      gammaKernel_weakAction A J α hs ht E hE 4 1 (by norm_num) hr
        (by have := hL.nonneg; have := hC.nonneg; positivity) _ hEm hEsup v hv a.val a.property]
    simp_rw [mul_add]
    rw [integral_add (kernelWeakAction_gamma_integrable A J α hs ht E hE hr _ hL0 v hv a.val a.property)
      (kernelWeakAction_gamma_integrable A J α hs ht E hE hr _ hErr v hv a.val a.property)]
    ring

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end

end
end
end

end

end OAI
