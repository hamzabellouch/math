import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeCandidateEvolution
import OAI.Geometry.TamingCompatibility.HeatFlow.HodgeBoundedWeakHeat
import OAI.Geometry.TamingCompatibility.Hodge.HodgeJointPartition

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.VolterraKernel
open MeasureTheory Set VolterraBounds
variable {X B : Type*} [MeasurableSpace X] [PseudoMetricSpace X] [NormedRing B]
  (μ : Measure X)

lemma HeatBound.weight_zero {N : ℕ} {T A : ℝ} {K : Kernel (X := X) (B := B)}
    (h : HeatBound μ N T A K) : HeatBound μ 0 T A K := by
  have hb (t : ℝ) (ht : t ∈ Ioc 0 T) (x y : X) :
      ‖K t x y‖ ≤ weight N t x y*‖K t x y‖ := by
    exact le_mul_of_one_le_left (norm_nonneg _) (weight_one_le N ht.1 x y)
  have hr (t : ℝ) (ht : t ∈ Ioc 0 T) (x : X) :
      Integrable (fun y => ‖K t x y‖) μ := by
    apply (h.row_int t ht x).mono' (((kernel_section K h.measurable t).comp_measurable
      (measurable_const.prodMk measurable_id)).norm.aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun y => by simpa using hb t ht x y
  have hc (t : ℝ) (ht : t ∈ Ioc 0 T) (y : X) :
      Integrable (fun x => ‖K t x y‖) μ := by
    apply (h.col_int t ht y).mono' (((kernel_section K h.measurable t).comp_measurable
      (measurable_id.prodMk measurable_const)).norm.aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun x => by simpa using hb t ht x y
  refine ⟨h.measurable,h.nonneg,?_,?_,?_,?_,?_⟩
  · intro t ht x y
    simpa only [weight,pow_zero,one_mul] using (hb t ht x y).trans (h.sup t ht x y)
  · intro t ht x
    simpa only [weight,pow_zero,one_mul] using hr t ht x
  · intro t ht x
    simpa only [weight,pow_zero,one_mul] using
      (integral_mono (hr t ht x) (h.row_int t ht x) (fun y => hb t ht x y)).trans (h.row t ht x)
  · intro t ht y
    simpa only [weight,pow_zero,one_mul] using hc t ht y
  · intro t ht y
    simpa only [weight,pow_zero,one_mul] using
      (integral_mono (hc t ht y) (h.col_int t ht y) (fun x => hb t ht x y)).trans (h.col t ht y)

end TamingCompatibility.GeometricHilbert.VolterraKernel

end
end

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
lemma globalCandidate_eq_spectral (n : ℕ) :
    let := geometricMetricSpace J α hs ht
    ∃ T L C : ℝ, 0 < T ∧ T ≤ 1 ∧
      VolterraKernel.HeatBound (geometricVolume A J α) n T L (globalLeading J α ht A E) ∧
      VolterraKernel.HeatBound (geometricVolume A J α) n T C (globalCorrection J α ht A E T) ∧
      ∀ v : X → FrameSpace A, Continuous v →
      ∃ f : L2 A J α hs ht true,
        (∀ a : PreL2 A J α hs ht true,
          ⟪f,smoothL2 A J α hs ht true a⟫ =
            ∫ y, framePairing A J α ht E a.val y (v y) ∂geometricVolume A J α) ∧
        (∀ a : PreL2 A J α hs ht true, ∀ t ∈ Ioc 0 T,
          ⟪hodgeSpectralHeat A J α hs ht D hD t f,smoothL2 A J α hs ht true a⟫ =
            kernelWeakAction A J α ht E (globalLeading J α ht A E) v a.val t +
            kernelWeakAction A J α ht E (globalError J α ht A E T) v a.val t) := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  let := geometricVolume_finite A J α hs ht
  obtain ⟨T,L,C,hT,hT1,hL,hC,hcancel⟩ := globalCorrection_small_bound J α hs ht A E hE n
  refine ⟨T,L,C,hT,hT1,hL,hC,?_⟩
  intro v hv
  obtain ⟨f,U,M,hM,hzero,hbound,hf,hpair,hcont,hweak⟩ :=
    globalCandidate_evolution_of_bounds A J α hs ht E hE hT hT1
      (hL.weight_zero _) (hC.weight_zero _) hcancel v hv
  have he := hodgeBoundedWeakHeat_eq_spectral A J α hs ht D hD f U hT.le hM hbound hcont hzero hweak
  refine ⟨f,hf,?_⟩
  intro a t ht'
  rw [← he t ⟨ht'.1.le,ht'.2⟩]
  exact hpair a t ht'

lemma exists_same_heat_parametrix :
    ∃ (A : FiniteCharts X)
      (_hE : ∀ p : A.centers, tsupport (A.partition p) ⊆ (parametrixData J α hs ht p.val).source)
      (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (HodgeChart.data J α hs ht p.val).source),
      ∀ n : ℕ, let := geometricMetricSpace J α hs ht
      ∃ T L C : ℝ, 0 < T ∧ T ≤ 1 ∧
        VolterraKernel.HeatBound (geometricVolume A J α) n T L
          (globalLeading J α ht A (fun p => parametrixData J α hs ht p.val)) ∧
        VolterraKernel.HeatBound (geometricVolume A J α) n T C
          (globalCorrection J α ht A (fun p => parametrixData J α hs ht p.val) T) ∧
        ∀ v : X → FrameSpace A, Continuous v →
        ∃ f : L2 A J α hs ht true,
          (∀ a : PreL2 A J α hs ht true,
            ⟪f,smoothL2 A J α hs ht true a⟫ =
              ∫ y, framePairing A J α ht (fun p => parametrixData J α hs ht p.val)
                a.val y (v y) ∂geometricVolume A J α) ∧
          (∀ a : PreL2 A J α hs ht true, ∀ t ∈ Ioc 0 T,
            ⟪hodgeSpectralHeat A J α hs ht (fun p => HodgeChart.data J α hs ht p.val) hD t f,
              smoothL2 A J α hs ht true a⟫ =
              kernelWeakAction A J α ht (fun p => parametrixData J α hs ht p.val)
                (globalLeading J α ht A (fun p => parametrixData J α hs ht p.val)) v a.val t +
              kernelWeakAction A J α ht (fun p => parametrixData J α hs ht p.val)
                (globalError J α ht A (fun p => parametrixData J α hs ht p.val) T) v a.val t) := by
  obtain ⟨A,hE,hD⟩ := finite_joint_partition J α hs ht
  exact ⟨A,hE,hD,fun n => globalCandidate_eq_spectral A J α hs ht _ hE _ hD n⟩

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
