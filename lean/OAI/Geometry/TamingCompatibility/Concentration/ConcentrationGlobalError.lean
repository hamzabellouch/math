import Mathlib
import OAI.Geometry.TamingCompatibility.Concentration.ConcentrationPatchQ
import OAI.Geometry.TamingCompatibility.Charts.ManifoldScalarCalculus

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory Hermitian Concentration
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
  (G : ∀ p : A.centers, GeometricChart.Data J α ht p.val)
  (hG : ∀ p, tsupport (A.partition p) ⊆ (G p).source)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

omit [ConnectedSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
lemma globalConcentration_wedge
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    {r : ℝ} (hr : 0 < r) (θ : Form X 1) :
    ManifoldForms.wedgeOne (scalarDifferential (globalConcentration A J α hs ht E μ r)) θ =
      ∑ p : A.centers, ManifoldForms.wedgeOne (scalarDifferential (concentrationPatch A J α hs ht E μ p r)) θ := by
  classical
  rw [globalConcentration,scalarDifferential_sum _ _
    (fun p _ => (concentrationPatch_smooth A J α hs ht E μ p hr).mdifferentiable (by simp)),wedgeOne_sum_left]

include hE hD hG in
lemma globalConcentration_current_control
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0)
    (Q : L2 A J α hs ht true)
    (hT : ∀ a : smoothForms X 2, IsClosed a.val →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ a + ⟪Q,smoothL2 A J α hs ht true a⟫ = 0) :
    ∃ e : ℝ → MetricUnit (hermitianMetric J α hs ht) → ℝ,
      (∀ r, 0 < r → ∀ u, 0 ≤ e r u) ∧
      (∀ r, 0 < r → Integrable (e r) μ) ∧
      Tendsto (fun r => ∫ u, e r u ∂μ) (𝓝[>] (0:ℝ)) (𝓝 0) ∧
      ∀ θ : smoothForms X 1, ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → ∀ u,
        |eval (ManifoldForms.wedgeOne (scalarDifferential (globalConcentration A J α hs ht E μ r)) θ.val)
          u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2)| ≤
        C*(globalConcentration A J α hs ht E μ r u.val.proj+e r u) := by
  classical
  choose e he hi h0 hb using fun p => concentrationPatch_error_control A J α hs ht E hE D hD G hG μ hann Q hT p
  let err := fun r u => ∑ p : A.centers, e p r u
  have hn (r) (hr : 0 < r) (u) : 0 ≤ err r u := Finset.sum_nonneg (fun p _ => he p r hr u)
  have hin (r) (hr : 0 < r) : Integrable (err r) μ := integrable_finsetSum _ (fun p _ => hi p r hr)
  have hlim : Tendsto (fun r => ∫ u, err r u ∂μ) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hh := tendsto_finsetSum Finset.univ (fun p _ => h0 p)
    simp only [Finset.sum_const_zero] at hh
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (integral_finsetSum _ (fun p _ => hi p r hr)).symm
  refine ⟨err,hn,hin,hlim,fun θ => ?_⟩
  choose C hC hbound using fun p => hb p θ
  refine ⟨∑ p, C p,Finset.sum_nonneg (fun p _ => hC p),fun r hr u => ?_⟩
  rw [globalConcentration_wedge A J α hs ht E μ hr θ.val]
  have heval : eval (∑ p : A.centers, ManifoldForms.wedgeOne (scalarDifferential (concentrationPatch A J α hs ht E μ p r)) θ.val)
      u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2) =
      ∑ p : A.centers, eval (ManifoldForms.wedgeOne (scalarDifferential (concentrationPatch A J α hs ht E μ p r)) θ.val)
        u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2) := by
    simp only [eval,Finset.sum_apply]
    erw [ContinuousAlternatingMap.sum_apply]
  rw [heval,Finset.sum_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro p _
  have hep : e p r u ≤ err r u := Finset.single_le_sum (fun i _ => he i r hr u) (Finset.mem_univ p)
  exact (hbound p r hr u).trans (mul_le_mul_of_nonneg_left (add_le_add_right hep _) (hC p))

include hE in
lemma globalConcentration_Q_control
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0)
    (Q : L2 A J α hs ht true) :
    ∃ e : ℝ → X → ℝ,
      (∀ r, 0 < r → ∀ x, 0 ≤ e r x) ∧
      (∀ r, 0 < r → Integrable (e r) (geometricVolume A J α)) ∧
      Tendsto (fun r => ∫ x, e r x ∂geometricVolume A J α) (𝓝[>] (0:ℝ)) (𝓝 0) ∧
      ∀ θ : smoothForms X 1, ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ x,
        ‖l2Coefficients A J α hs ht E hE Q x‖ *
          ‖normalizedFrameEncode A J α ht E x
            (ManifoldForms.wedgeOne (scalarDifferential (globalConcentration A J α hs ht E μ r)) θ.val x)‖ ≤ C*e r x := by
  classical
  choose e he hi h0 hb using fun p => concentrationPatch_Q_control A J α hs ht E hE μ hann Q p
  let err := fun r x => ∑ p : A.centers, e p r x
  have hn (r) (hr : 0 < r) (x) : 0 ≤ err r x := Finset.sum_nonneg (fun p _ => he p r hr x)
  have hin (r) (hr : 0 < r) : Integrable (err r) (geometricVolume A J α) := integrable_finsetSum _ (fun p _ => hi p r hr)
  have hlim : Tendsto (fun r => ∫ x, err r x ∂geometricVolume A J α) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hh := tendsto_finsetSum Finset.univ (fun p _ => h0 p)
    simp only [Finset.sum_const_zero] at hh
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (integral_finsetSum _ (fun p _ => hi p r hr)).symm
  refine ⟨err,hn,hin,hlim,fun θ => ?_⟩
  choose C hC hbound using fun p => hb p θ
  refine ⟨∑ p, C p,Finset.sum_nonneg (fun p _ => hC p),fun r hr hr1 x => ?_⟩
  rw [globalConcentration_wedge A J α hs ht E μ hr θ.val]
  simp only [Finset.sum_apply]
  erw [_root_.map_sum]
  have hh := mul_le_mul_of_nonneg_left (norm_sum_le Finset.univ
    (fun p : A.centers => normalizedFrameEncode A J α ht E x
      (ManifoldForms.wedgeOne (scalarDifferential (concentrationPatch A J α hs ht E μ p r)) θ.val x)))
    (norm_nonneg (l2Coefficients A J α hs ht E hE Q x))
  rw [Finset.mul_sum] at hh
  apply hh.trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p _
  have hep : e p r x ≤ err r x := Finset.single_le_sum (fun i _ => he i r hr x) (Finset.mem_univ p)
  exact (hbound p r hr hr1 x).trans (mul_le_mul_of_nonneg_left hep (hC p))
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory PlaneVariation Concentration Hermitian
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

omit [ConnectedSpace X] in
lemma concentrationPatch_integrable
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    (p : A.centers) {r : ℝ} (hr : 0 < r) :
    Integrable (concentrationPatch A J α hs ht E μ p r) (geometricVolume A J α) := by
  let := geometricVolume_finite A J α hs ht
  exact (concentrationPatch_smooth A J α hs ht E μ p hr).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

omit [ConnectedSpace X] in
lemma globalConcentration_integrable
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    {r : ℝ} (hr : 0 < r) :
    Integrable (globalConcentration A J α hs ht E μ r) (geometricVolume A J α) := by
  let := geometricVolume_finite A J α hs ht
  exact (globalConcentration_smooth A J α hs ht E μ hr).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

include hE in
lemma concentrationPatch_volume_growth
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (p : A.centers) : ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r →
      (∫ x, concentrationPatch A J α hs ht E μ p r x ∂geometricVolume A J α) ≤ C*r^2 := by
  obtain ⟨C,L,hC,hL,hbound⟩ := localConcentration_physical_bound A J α hs ht E hE μ p
  obtain ⟨B,hB,hvol⟩ := physicalProfileMass_volume_growth A J α hs ht μ
  refine ⟨C*B*L^4,by positivity,fun r hr => ?_⟩
  have hp (x : X) : concentrationPatch A J α hs ht E μ p r x ≤
      (C/r^2)*physicalProfileMass J α hs ht μ (L*r) x := by
    rw [concentrationPatch_apply]
    by_cases hx : x ∈ tsupport (A.partition p)
    · exact (mul_le_of_le_one_left (localConcentration_nonneg A J α hs ht E μ p r _) (A.partition.le_one _ _)).trans
        (hbound x hx r hr)
    · rw [image_eq_zero_of_notMem_tsupport hx,zero_mul]
      exact mul_nonneg (by positivity) (physicalProfileMass_nonneg J α hs ht μ _ _)
  calc
    _ ≤ ∫ x, (C/r^2)*physicalProfileMass J α hs ht μ (L*r) x ∂geometricVolume A J α :=
      integral_mono (concentrationPatch_integrable A J α hs ht E μ p hr)
        ((physicalProfileMass_integrable A J α hs ht μ (mul_pos hL hr)).const_mul _) hp
    _ = (C/r^2)*(∫ x, physicalProfileMass J α hs ht μ (L*r) x ∂geometricVolume A J α) := integral_const_mul _ _
    _ ≤ (C/r^2)*(B*(L*r)^4) := mul_le_mul_of_nonneg_left (hvol (L*r) (mul_pos hL hr)) (by positivity)
    _ = _ := by field_simp

include hE in
lemma globalConcentration_volume_growth
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r →
      (∫ x, globalConcentration A J α hs ht E μ r x ∂geometricVolume A J α) ≤ C*r^2 := by
  classical
  choose C hC hbound using concentrationPatch_volume_growth A J α hs ht E hE μ
  refine ⟨∑ p, C p,Finset.sum_nonneg (fun p _ => hC p),fun r hr => ?_⟩
  simp only [globalConcentration,Finset.sum_apply]
  rw [integral_finsetSum _ (fun p _ => concentrationPatch_integrable A J α hs ht E μ p hr),Finset.sum_mul]
  exact Finset.sum_le_sum (fun p _ => hbound p r hr)

include hE in
lemma globalConcentration_volume_limit
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ] :
    Tendsto (fun r : ℝ => ∫ x, globalConcentration A J α hs ht E μ r x ∂geometricVolume A J α)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  obtain ⟨C,_,hbound⟩ := globalConcentration_volume_growth A J α hs ht E hE μ
  apply squeeze_zero' (Eventually.of_forall fun r => integral_nonneg (globalConcentration_nonneg A J α hs ht E μ r))
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact hbound r hr
  · have hid : Tendsto (fun r : ℝ => r) (𝓝[>] (0:ℝ)) (𝓝 0) := nhdsWithin_le_nhds
    simpa only [zero_pow (by decide : 2 ≠ 0),mul_zero] using (tendsto_const_nhds (x := C)).mul (hid.pow 2)
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
