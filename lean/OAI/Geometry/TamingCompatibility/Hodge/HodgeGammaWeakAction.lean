import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeContinuousParametrix

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

attribute [local irreducible] framePairing globalLeading globalResidual hodgeLaplacian
include hs hE in
lemma gammaKernel_weakAction (q k : ℕ) (hqk : q+k=5) {T r H : ℝ} (hr : 0 < r) (hH : 0 ≤ H)
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    (hKm : VolterraKernel.MeasurableKernel K)
    (hK : ∀ t ∈ Ioc 0 T, ∀ x y, ‖K t x y‖ ≤ H/t^k)
    (v : X → FrameSpace A) (hv : Continuous v) (a : TwoForm X) (ha : IsSmooth a) :
    (∫ y, ∫ x, framePairing A J α ht E a x
      (HodgeKernelBounds.gammaKernel K T r x y (v y))
        ∂geometricVolume A J α ∂geometricVolume A J α) =
      (1/120:ℝ) * ∫ s : ℝ in Ioc 0 (T/r^2), hodgeGammaWeight s *
        kernelWeakAction A J α ht E K v a (r^2*s) := by
  let := geometricMetricSpace J α hs ht
  let := geometricVolume_finite A J α hs ht
  obtain ⟨B,hB,hφ⟩ := framePairing_bound A J α hs ht E hE a ha
  obtain ⟨V₀,hV₀⟩ := isCompact_univ.exists_bound_of_continuousOn hv.continuousOn
  let V := max V₀ 0
  have hV : 0 ≤ V := le_max_right _ _
  have hvB (y : X) : ‖v y‖ ≤ V := (hV₀ y (mem_univ y)).trans (le_max_left _ _)
  let Θ : X × X → (FrameSpace A →L[ℝ] FrameSpace A) →L[ℝ] ℝ := fun p =>
    (framePairing A J α ht E a p.2).comp ((ContinuousLinearMap.apply ℝ (FrameSpace A)) (v p.1))
  have hΘc : Continuous Θ :=
    ((framePairing_continuous A J α hs ht E hE a ha).comp continuous_snd).clm_comp
      ((ContinuousLinearMap.apply ℝ (FrameSpace A)).continuous.comp (hv.comp continuous_fst))
  have hΘb (p : X × X) : ‖Θ p‖ ≤ B*V := by
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hB hV)
    intro L
    calc
      _ ≤ ‖framePairing A J α ht E a p.2‖ * ‖L (v p.1)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ B*(‖L‖*V) := mul_le_mul (hφ p.2)
        ((ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left (hvB p.1) (norm_nonneg _)))
        (norm_nonneg _) hB
      _ = _ := by ring
  have hh := HodgeKernelBounds.gammaKernel_pairing_iterated (geometricVolume A J α) q k hqk hr hH
    (fun t x y => K t y x)
    (hKm.comp_measurable (show Measurable (fun p : ℝ × X × X => (p.1,p.2.2,p.2.1)) by fun_prop))
    (fun t ht x y => hK t ht y x) Θ hΘc.stronglyMeasurable (mul_nonneg hB hV) hΘb
  exact hh

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

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

include hE in
lemma kernelWeakAction_gamma_integrable {T H r : ℝ} (hr : 0 < r)
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    (hK : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T H K)
    (v : X → FrameSpace A) (hv : Continuous v) (a : TwoForm X) (ha : IsSmooth a) :
    IntegrableOn (fun s : ℝ => hodgeGammaWeight s * kernelWeakAction A J α ht E K v a (r^2*s))
      (Ioc 0 (T/r^2)) := by
  let := geometricMetricSpace J α hs ht
  obtain ⟨V₀,hV₀⟩ := isCompact_univ.exists_bound_of_continuousOn hv.continuousOn
  let V := max V₀ 0
  have hV : 0 ≤ V := le_max_right _ _
  have hvB (y : X) : ‖v y‖ ≤ V := (hV₀ y (mem_univ y)).trans (le_max_left _ _)
  obtain ⟨B,_hB,hb⟩ := kernelInputTest_uniform_bound A J α hs ht E hE K hK a ha hV
  have hst (s : ℝ) (hs : s ∈ Ioc 0 (T/r^2)) : r^2*s ∈ Ioc 0 T :=
    ⟨mul_pos (sq_pos_of_pos hr) hs.1,by
      have h := (le_div_iff₀ (sq_pos_of_pos hr)).mp hs.2
      simpa only [mul_comm] using h⟩
  have hm := (kernelInputTest_time_measurable A J α hs ht E hE K hK.measurable a ha v
    hv.stronglyMeasurable).comp_measurable (show Measurable (fun s : ℝ => r^2*s) by fun_prop)
  have hi : IntegrableOn (fun s : ℝ => hodgeGammaWeight s * kernelInputTest A J α ht E K a (r^2*s) v)
      (Ioc 0 (T/r^2)) := by
    apply ((hodgeGammaWeight_integrable.mono_set (fun _ hx => hx.1)).mul_const B).mono'
      (hodgeGammaWeight_continuous.stronglyMeasurable.mul hm).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hsp
    change ‖hodgeGammaWeight s * kernelInputTest A J α ht E K a (r^2*s) v‖ ≤ hodgeGammaWeight s * B
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (hodgeGammaWeight_nonneg hsp.1.le)]
    exact mul_le_mul_of_nonneg_left (hb _ (hst s hsp) v hvB) (hodgeGammaWeight_nonneg hsp.1.le)
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hsp
  rw [kernelInputTest_eq_weakAction A J α hs ht E hE K hK a ha (hst s hsp) v]

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
