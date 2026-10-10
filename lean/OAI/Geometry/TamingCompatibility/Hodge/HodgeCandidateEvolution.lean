import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeInputLinearity
import OAI.Geometry.TamingCompatibility.Hodge.HodgeCandidateL2Bounds

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
attribute [local irreducible] framePairing globalLeading globalResidual hodgeLaplacian

include hE in
lemma globalCandidate_evolution_of_bounds {T L C : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hL : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T L (globalLeading J α ht A E))
    (hC : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T C (globalCorrection J α ht A E T))
    (hcancel : ∀ t ∈ Ioc 0 T, ∀ x y, globalResidual J α ht A E t x y +
      globalCorrection J α ht A E T t x y +
      VolterraKernel.convolution (geometricVolume A J α) (globalResidual J α ht A E)
        (globalCorrection J α ht A E T) t x y = 0)
    (v : X → FrameSpace A) (hv : Continuous v) :
    ∃ (f : L2 A J α hs ht true) (U : ℝ → L2 A J α hs ht true) (M : ℝ),
      0 ≤ M ∧ U 0 = f ∧ (∀ t ∈ Icc 0 T, ‖U t‖ ≤ M) ∧
      (∀ a : PreL2 A J α hs ht true,
        ⟪f,smoothL2 A J α hs ht true a⟫ =
          ∫ y, framePairing A J α ht E a.val y (v y) ∂geometricVolume A J α) ∧
      (∀ a : PreL2 A J α hs ht true, ∀ t ∈ Ioc 0 T,
        ⟪U t,smoothL2 A J α hs ht true a⟫ =
          kernelWeakAction A J α ht E (globalLeading J α ht A E) v a.val t +
          kernelWeakAction A J α ht E (globalError J α ht A E T) v a.val t) ∧
      (∀ a : PreL2 A J α hs ht true,
        ContinuousOn (fun t => ⟪U t,smoothL2 A J α hs ht true a⟫) (Icc 0 T)) ∧
      (∀ a : PreL2 A J α hs ht true, ∀ t ∈ Ioo 0 T,
        HasDerivAt (fun s => ⟪U s,smoothL2 A J α hs ht true a⟫)
          (-⟪U t,smoothL2 A J α hs ht true (hodgeLaplacian A J α hs ht a)⟫) t) := by
  let := geometricMetricSpace J α hs ht
  let := geometricVolume_finite A J α hs ht
  obtain ⟨f,U,M,hM,hzero,hbound,hf,hpair,_hini⟩ :=
    globalCandidate_L2_of_bounds A J α hs ht E hE hT hL hC v hv
  have hErr := VolterraKernel.convolution_heatBound (geometricVolume A J α) 0 hT.le _ _ hL hC
  obtain ⟨V₀,hV₀⟩ := isCompact_univ.exists_bound_of_continuousOn hv.continuousOn
  let V := max V₀ 0
  have hV : 0 ≤ V := le_max_right _ _
  have hvb (y : X) : ‖v y‖ ≤ V := (hV₀ y (mem_univ y)).trans (le_max_left _ _)
  have hp (a : PreL2 A J α hs ht true) (t : ℝ) (htp : t ∈ Ioc 0 T) :
      ⟪U t,smoothL2 A J α hs ht true a⟫ =
        kernelInputTest A J α ht E (globalLeading J α ht A E) a.val t v +
        kernelInputTest A J α ht E (globalError J α ht A E T) a.val t v := by
    rw [hpair a t htp]
    exact congrArg₂ (· + ·)
      (kernelInputTest_eq_weakAction A J α hs ht E hE _ hL a.val a.property htp v).symm
      (kernelInputTest_eq_weakAction A J α hs ht E hE _ hErr a.val a.property htp v).symm
  have hi (a : PreL2 A J α hs ht true) :
      IntegrableOn (fun t => ⟪U t,smoothL2 A J α hs ht true a⟫) (Icc 0 T) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioo]
    have hP := kernelInputTest_time_integrable A J α hs ht E hE _ hL a.val a.property
      le_rfl v hv.stronglyMeasurable hV hvb
    have hQ := kernelInputTest_time_integrable A J α hs ht E hE _ hErr a.val a.property
      le_rfl v hv.stronglyMeasurable hV hvb
    apply (hP.add hQ).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t htp
    exact (hp a t ⟨htp.1,htp.2.le⟩).symm
  have hprim (a : PreL2 A J α hs ht true) (t : ℝ) (htp : t ∈ Icc 0 T) :
      ⟪U t,smoothL2 A J α hs ht true a⟫ = ⟪f,smoothL2 A J α hs ht true a⟫ -
        ∫ s in Ioo 0 t, ⟪U s,smoothL2 A J α hs ht true (hodgeLaplacian A J α hs ht a)⟫ := by
    by_cases hz : t=0
    · simp [hz,hzero]
    have htpos : t ∈ Ioc 0 T := ⟨lt_of_le_of_ne htp.1 (Ne.symm hz),htp.2⟩
    rw [hp a t htpos,hf a]
    have hh := candidate_primitive_of_cancellation A J α hs ht E hE
      (globalCorrection J α ht A E T) hT hT1 hC hcancel
      v hv.stronglyMeasurable hV hvb a htpos
    apply hh.trans
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioo
    intro s hsp
    exact (hp (hodgeLaplacian A J α hs ht a) s ⟨hsp.1,hsp.2.le.trans htp.2⟩).symm
  obtain ⟨hc,hd⟩ := WeakHeat.of_primitive (hodgeLaplacian A J α hs ht)
    (fun a t => ⟪U t,smoothL2 A J α hs ht true a⟫)
    (fun a => ⟪f,smoothL2 A J α hs ht true a⟫) hT.le hi hprim
  exact ⟨f,U,M,hM,hzero,hbound,hf,hpair,hc,hd⟩

include hE in
lemma globalCandidate_evolution :
    ∃ T : ℝ, 0 < T ∧ T ≤ 1 ∧ ∀ v : X → FrameSpace A, Continuous v →
    ∃ (f : L2 A J α hs ht true) (U : ℝ → L2 A J α hs ht true) (M : ℝ),
      0 ≤ M ∧ U 0 = f ∧ (∀ t ∈ Icc 0 T, ‖U t‖ ≤ M) ∧
      (∀ a : PreL2 A J α hs ht true,
        ⟪f,smoothL2 A J α hs ht true a⟫ =
          ∫ y, framePairing A J α ht E a.val y (v y) ∂geometricVolume A J α) ∧
      (∀ a : PreL2 A J α hs ht true, ∀ t ∈ Ioc 0 T,
        ⟪U t,smoothL2 A J α hs ht true a⟫ =
          kernelWeakAction A J α ht E (globalLeading J α ht A E) v a.val t +
          kernelWeakAction A J α ht E (globalError J α ht A E T) v a.val t) ∧
      (∀ a : PreL2 A J α hs ht true,
        ContinuousOn (fun t => ⟪U t,smoothL2 A J α hs ht true a⟫) (Icc 0 T)) ∧
      (∀ a : PreL2 A J α hs ht true, ∀ t ∈ Ioo 0 T,
        HasDerivAt (fun s => ⟪U s,smoothL2 A J α hs ht true a⟫)
          (-⟪U t,smoothL2 A J α hs ht true (hodgeLaplacian A J α hs ht a)⟫) t) := by
  let := geometricMetricSpace J α hs ht
  let := geometricVolume_finite A J α hs ht
  obtain ⟨T,L,C,hT,hT1,hL,hC,hcancel⟩ := globalCorrection_small_bound J α hs ht A E hE 0
  exact ⟨T,hT,hT1,fun v hv =>
    globalCandidate_evolution_of_bounds A J α hs ht E hE hT hT1 hL hC hcancel v hv⟩

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
