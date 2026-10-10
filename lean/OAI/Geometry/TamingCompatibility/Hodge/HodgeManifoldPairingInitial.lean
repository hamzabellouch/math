import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeKernelWeakAction

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeNormalSymbol HodgeFrame Set Filter MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] Classical.propDecidable
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

include hs hE in
lemma leadingSliceForm_initial (p : A.centers) (q : Space) (u : W)
    (a : TwoForm X) (ha : IsSmooth a) :
    Tendsto (fun t : ℝ => ∫ x, GeometricAdjoint.pairing J α ht a
        (leadingSliceForm J α ht A E p q t u) x ∂geometricVolume A J α)
      (𝓝[>] 0) (𝓝 (coordinatePartition A p q * ⟪HodgeChart.rawVector J α ht p.val (E p).chart a q,u⟫)) := by
  by_cases hq : q ∈ Metric.closedBall (extChartAt Model p.val p.val) (E p).radius
  · have hh := (E p).cutoff_form_initial hs hq (coordinatePartition A p q • u) a ha
    rw [inner_smul_right] at hh
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with t htp
    rw [leadingSliceForm,HodgeChart.pairing_manifoldTest_integral J α ht p.val (E p).chart A hs ha
      (leadingSlice_smooth J α ht A E hE hs p q htp u)
      (leadingSlice_compact J α ht A E p q t u)
      (leadingSlice_domain J α ht A E p hq t u),leadingSlice_pairing_integral J α ht A E p hq]
    rfl
  · have hz : coordinatePartition A p q = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hq (coordinatePartition_centerSupport J α ht A E hE p h))
    simp only [leadingSliceForm_zero_center J α ht A E p hz,pairing_zero_form,
      integral_zero,hz,zero_mul]
    exact tendsto_const_nhds

include hs hE in
lemma leadingFiberForm_initial (p : A.centers) (y : X) (v : FrameSpace A)
    (a : TwoForm X) (ha : IsSmooth a) :
    Tendsto (fun t : ℝ => ∫ x, GeometricAdjoint.pairing J α ht a
        (leadingFiberForm J α ht A E p y t v) x ∂geometricVolume A J α)
      (𝓝[>] 0) (𝓝 (A.partition p y * GeometricAdjoint.pairing J α ht a
        (fun x => frameDecode J α ht A E x v) y)) := by
  unfold leadingFiberForm
  by_cases hy : y ∈ (extChartAt Model p.val).source
  · simp only [ite_eq_left hy]
    have hh := leadingSliceForm_initial A J α hs ht E hE p (extChartAt Model p.val y)
      (coordinateDecode J α ht A E p (extChartAt Model p.val y) v) a ha
    rw [coordinatePartition_apply A p hy] at hh
    by_cases hz : A.partition p y = 0
    · simpa only [hz,zero_mul] using hh
    · have hsupp : y ∈ tsupport (A.partition p) := subset_tsupport _ hz
      have hc : extChartAt Model p.val y ∈ Metric.closedBall (extChartAt Model p.val p.val) (E p).radius :=
        (Metric.closedBall_subset_closedBall (by linarith [(E p).radius_pos]))
          ((E p).source_image_subset ⟨y,hE p hsupp,rfl⟩)
      have hyd := (E p).actual_subset ((E p).centers_actual hc)
      have hpair : ⟪HodgeChart.rawVector J α ht p.val (E p).chart a (extChartAt Model p.val y),
          coordinateDecode J α ht A E p (extChartAt Model p.val y) v⟫ =
          GeometricAdjoint.pairing J α ht a (fun x => frameDecode J α ht A E x v) y := by
        rw [coordinateDecode_rawVector]
        unfold HodgeChart.rawVector
        rw [coordinates_pairing _ (by simp [Space]) _ ((E p).chart.frame_gram _ hyd)]
        have hp := GeometricAdjoint.pairing_two_chart J α ht p.val a
          (show TwoForm X from fun x => frameDecode J α ht A E x v)
          ((extChartAt Model p.val).map_source hy)
        rw [(extChartAt Model p.val).left_inv hy] at hp
        exact hp
      rwa [hpair] at hh
  · have hz : A.partition p y = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hy (A.subordinate p h))
    simp only [ite_eq_right hy,pairing_zero_form,integral_zero,hz,zero_mul]
    exact tendsto_const_nhds

include hs hE in
lemma leadingKernelForm_initial (y : X) (v : FrameSpace A)
    (a : TwoForm X) (ha : IsSmooth a) :
    Tendsto (fun t : ℝ => ∫ x, GeometricAdjoint.pairing J α ht a
        (leadingKernelForm J α ht A E t y v) x ∂geometricVolume A J α)
      (𝓝[>] 0) (𝓝 (GeometricAdjoint.pairing J α ht a
        (fun x => frameDecode J α ht A E x v) y)) := by
  have hh := tendsto_finsetSum (s := Finset.univ) (fun (p : A.centers) _ => leadingFiberForm_initial A J α hs ht E hE p y v a ha)
  rw [← Finset.sum_mul, partition_sum A y,one_mul] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with t htp
  change 0 < t at htp
  rw [leadingKernelForm,ite_eq_left htp]
  exact (integral_pairing_sum A J α hs ht _ a ha _ (fun p _ =>
    leadingFiberForm_smooth J α ht A E hE hs p y htp v)).symm

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldVolume ManifoldLocalization Set MeasureTheory Filter
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
  (A : FiniteCharts X)

include hs ht in
omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [T2Space X] in
lemma chart_density_compact_bound (p : X) (L : Set Space) (hL : IsCompact L)
    (hLt : L ⊆ (extChartAt Model p).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ L, chartDensity J α p z ≤ C := by
  obtain ⟨C,hC⟩ := hL.exists_bound_of_continuousOn ((chartDensity_smooth J α hs ht p).continuousOn.mono hLt)
  exact ⟨max C 0,le_max_right _ _,fun z hz => (le_abs_self _).trans ((hC z hz).trans (le_max_left _ _))⟩

include hs ht in

lemma integral_chart_bound (p : X) (L : Set Space) (hL : IsCompact L)
    (hLt : L ⊆ (extChartAt Model p).target) (D : ℝ) (hD : 0 ≤ D)
    (hDb : ∀ z ∈ L, chartDensity J α p z ≤ D)
    (f : X → ℝ) (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    (hfs : Function.support f ⊆ (extChartAt Model p).symm '' L)
    (G : Space → ℝ) (hGi : Integrable G) (hG0 : ∀ z, 0 ≤ G z)
    (hGf : ∀ z ∈ (extChartAt Model p).target, f ((extChartAt Model p).symm z) ≤ G z) :
    (∫ x, f x ∂geometricVolume A J α) ≤ D*(∫ z, G z) := by
  have hLc : IsCompact ((extChartAt Model p).symm '' L) :=
    hL.image_of_continuousOn ((continuousOn_extChartAt_symm p).mono hLt)
  have hts : tsupport f ⊆ (extChartAt Model p).symm '' L := closure_minimal hfs hLc.isClosed
  have hts' : tsupport f ⊆ (extChartAt Model p).source := by
    intro x hx
    obtain ⟨z,hz,rfl⟩ := hts hx
    exact (extChartAt Model p).map_target (hLt hz)
  have hcgi := coordinateIntegrand_integrable J α hs ht p f hf hts'
  have hpoint (z : Space) : coordinateIntegrand J α p f z ≤ D*G z := by
    by_cases hzt : z ∈ (extChartAt Model p).target
    · rw [coordinateIntegrand,Set.indicator_of_mem hzt]
      by_cases hz : z ∈ L
      · exact mul_le_mul (hDb z hz) (hGf z hzt) (hf0 _) hD
      · have hfz : f ((extChartAt Model p).symm z) = 0 := by
          apply Function.notMem_support.mp
          intro hh
          obtain ⟨w,hw,he⟩ := hfs hh
          have he' := congrArg (extChartAt Model p) he
          rw [(extChartAt Model p).right_inv (hLt hw),(extChartAt Model p).right_inv hzt] at he'
          exact hz (he' ▸ hw)
        rw [hfz,mul_zero]
        exact mul_nonneg hD (hG0 z)
    · rw [coordinateIntegrand,Set.indicator_of_notMem hzt]
      exact mul_nonneg hD (hG0 z)
  rw [integral_geometricVolume_coordinate A J α hs ht p f hf hts',
    ← integral_indicator (isOpen_extChartAt_target p).measurableSet]
  change (∫ z, coordinateIntegrand J α p f z) ≤ _
  calc
    _ ≤ ∫ z, D*G z := integral_mono hcgi (hGi.const_mul D) hpoint
    _ = _ := integral_const_mul _ _

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
