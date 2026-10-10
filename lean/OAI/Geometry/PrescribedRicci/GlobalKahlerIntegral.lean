import Mathlib
import OAI.Geometry.PrescribedRicci.KahlerIntegration

namespace OAI

/-! Global Kahler Integral. -/

section

 

noncomputable section
open Matrix Filter Set Topology MeasureTheory
open scoped ContDiff ComplexOrder Classical
namespace Anticanonical.SourceSmooth
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}

namespace KaehlerMetric

def localizeFunction (i : Fin A.count) (f : X → ℝ) (z : Coordinates d) : ℝ :=
  if z ∈ (A.chart i).target then f ((A.chart i).symm z) else 0

lemma localizeFunction_support (i : Fin A.count) (f : X → ℝ) :
    Function.support (localizeFunction (A := A) i f) ⊆ (A.chart i) '' tsupport f := by
  intro z hz
  change localizeFunction i f z ≠ 0 at hz
  by_cases ht : z ∈ (A.chart i).target
  · have hh : f ((A.chart i).symm z) ≠ 0 := by simpa [localizeFunction, ht] using hz
    exact ⟨(A.chart i).symm z, subset_tsupport _ hh, (A.chart i).right_inv ht⟩
  · exact (hz (ite_eq_right ht)).elim

lemma localizeFunction_continuous_compact [T2Space X] [CompactSpace X]
    (i : Fin A.count) {f : X → ℝ} (hf : Continuous f)
    (hs : tsupport f ⊆ (A.chart i).source) :
    Continuous (localizeFunction (A := A) i f) ∧
      HasCompactSupport (localizeFunction (A := A) i f) ∧
      tsupport (localizeFunction (A := A) i f) ⊆ (A.chart i).target := by
  let e := A.chart i
  let K := e '' tsupport f
  have hK : IsCompact K := (isClosed_tsupport _).isCompact.image_of_continuousOn
    (e.continuousOn.mono hs)
  have hsub : Function.support (localizeFunction i f) ⊆ K := localizeFunction_support i f
  have hts : tsupport (localizeFunction i f) ⊆ K := closure_minimal hsub hK.isClosed
  refine ⟨?_, HasCompactSupport.of_support_subset_isCompact hK hsub, ?_⟩
  · rw [continuous_iff_continuousAt]
    intro z
    by_cases hz : z ∈ e.target
    · apply (hf.continuousAt.comp ((e.continuousOn_symm z hz).continuousAt
        (e.open_target.mem_nhds hz))).congr
      filter_upwards [e.open_target.mem_nhds hz] with y hy
      exact (ite_eq_left hy).symm
    · have hzK : z ∉ K := by
        rintro ⟨x, hx, rfl⟩
        exact hz (e.mapsTo (hs hx))
      apply (continuousAt_const (y := (0 : ℝ))).congr
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hzK] with y hy
      exact (Function.notMem_support.mp (fun h => hy (hsub h))).symm
  · rintro z hz
    obtain ⟨x, hx, rfl⟩ := hts hz
    exact e.mapsTo (hs hx)

lemma continuous_real_mul_on_tsupport {E : Type*} [TopologicalSpace E] {f h : E → ℝ}
    (hf : Continuous f) (hh : ∀ z ∈ tsupport f, ContinuousAt h z) :
    Continuous (fun z => f z * h z) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z ∈ tsupport f
  · exact hf.continuousAt.mul (hh z hz)
  · apply (continuousAt_const (y := (0 : ℝ))).congr
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz] with y hy
    simp only [hy, zero_mul, Pi.zero_apply]

lemma chart_integrable [T2Space X] [CompactSpace X] (g : KaehlerMetric A)
    (i : Fin A.count) {f : X → ℝ} (hf : Continuous f)
    (hs : tsupport f ⊆ (A.chart i).source) :
    IntegrableOn (fun z => f ((A.chart i).symm z) * g.volumeCoefficient i z)
      (A.chart i).target := by
  obtain ⟨hl, hc, ht⟩ := localizeFunction_continuous_compact i hf hs
  have hi : Integrable (fun z => localizeFunction i f z * g.volumeCoefficient i z) :=
    (continuous_real_mul_on_tsupport hl (fun z hz =>
    ((g.volumeCoefficient_smooth i).continuousOn z (ht hz)).continuousAt
      ((A.chart i).open_target.mem_nhds (ht hz)))).integrable_of_hasCompactSupport hc.mul_right
  apply hi.integrableOn.congr_fun _ (A.chart i).open_target.measurableSet
  intro z hz
  simp only [localizeFunction, ite_eq_left hz]

lemma chartIntegral_linear_add [T2Space X] [CompactSpace X] (g : KaehlerMetric A)
    (i : Fin A.count) {f h : X → ℝ} (hf : Continuous f) (hh : Continuous h)
    (hsf : tsupport f ⊆ (A.chart i).source) (hsh : tsupport h ⊆ (A.chart i).source) :
    g.chartIntegral i (fun x => f x + h x) = g.chartIntegral i f + g.chartIntegral i h := by
  simp only [chartIntegral, add_mul]
  exact integral_add (g.chart_integrable i hf hsf) (g.chart_integrable i hh hsh)

lemma chartIntegral_sum [T2Space X] [CompactSpace X] (g : KaehlerMetric A)
    (i : Fin A.count) {ι : Type*} (s : Finset ι) (f : ι → X → ℝ)
    (hf : ∀ k ∈ s, Continuous (f k)) (hs : ∀ k ∈ s, tsupport (f k) ⊆ (A.chart i).source) :
    g.chartIntegral i (fun x => ∑ k ∈ s, f k x) = ∑ k ∈ s, g.chartIntegral i (f k) := by
  simp only [chartIntegral, Finset.sum_mul]
  exact integral_finsetSum s (fun k hk => g.chart_integrable i (hf k hk) (hs k hk))

def chartPartition [T2Space X] [CompactSpace X] : Fin A.count → SmoothRealFunction A :=
  A.exists_smooth_partition.choose

lemma chartPartition_nonneg [T2Space X] [CompactSpace X] (i : Fin A.count) (x : X) :
    0 ≤ (chartPartition (A := A) i).value x := A.exists_smooth_partition.choose_spec.1 i x

lemma chartPartition_sum [T2Space X] [CompactSpace X] (x : X) :
    ∑ i, (chartPartition (A := A) i).value x = 1 := A.exists_smooth_partition.choose_spec.2.1 x

lemma chartPartition_support [T2Space X] [CompactSpace X] (i : Fin A.count) :
    tsupport (chartPartition (A := A) i).value ⊆ (A.chart i).source :=
  A.exists_smooth_partition.choose_spec.2.2 i

 

def integral [T2Space X] [CompactSpace X] (g : KaehlerMetric A) (f : X → ℝ) : ℝ :=
  ∑ i, g.chartIntegral i (fun x => (chartPartition i).value x * f x)

lemma integral_chart [T2Space X] [CompactSpace X] (g : KaehlerMetric A)
    (j : Fin A.count) {f : X → ℝ} (hf : Continuous f)
    (hs : tsupport f ⊆ (A.chart j).source) : g.integral f = g.chartIntegral j f := by
  unfold integral
  have he : ∀ i, g.chartIntegral i (fun x => (chartPartition i).value x * f x) =
      g.chartIntegral j (fun x => (chartPartition i).value x * f x) := by
    intro i
    apply g.chartIntegral_eq
    · exact fun x hx => chartPartition_support i
        (subset_tsupport _ (Function.support_mul_subset_left _ _ hx))
    · exact fun x hx => hs (subset_tsupport _ (Function.support_mul_subset_right _ _ hx))
  simp_rw [he]
  rw [← g.chartIntegral_sum j Finset.univ (fun i x => (chartPartition i).value x * f x)
    (fun i _ => (chartPartition i).continuous.fun_mul hf)
    (fun i _ => tsupport_mul_subset_right.trans hs)]
  congr 1
  funext x
  rw [← Finset.sum_mul, chartPartition_sum, one_mul]

lemma integral_add [T2Space X] [CompactSpace X] (g : KaehlerMetric A)
    {f h : X → ℝ} (hf : Continuous f) (hh : Continuous h) :
    g.integral (fun x => f x + h x) = g.integral f + g.integral h := by
  unfold integral
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [mul_add]
  exact g.chartIntegral_linear_add i ((chartPartition i).continuous.mul hf)
    ((chartPartition i).continuous.mul hh)
    (tsupport_mul_subset_left.trans (chartPartition_support i))
    (tsupport_mul_subset_left.trans (chartPartition_support i))

lemma integral_const_mul [T2Space X] [CompactSpace X] (g : KaehlerMetric A)
    (c : ℝ) (f : X → ℝ) : g.integral (fun x => c * f x) = c * g.integral f := by
  simp only [integral, chartIntegral, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [show ∀ z, (chartPartition i).value ((A.chart i).symm z) * (c * f ((A.chart i).symm z)) *
      g.volumeCoefficient i z = c * ((chartPartition i).value ((A.chart i).symm z) *
      f ((A.chart i).symm z) * g.volumeCoefficient i z) by intro z; ring]
  exact MeasureTheory.integral_const_mul c _

lemma integral_sum [T2Space X] [CompactSpace X] (g : KaehlerMetric A)
    {ι : Type*} (s : Finset ι) (f : ι → X → ℝ) (hf : ∀ k ∈ s, Continuous (f k)) :
    g.integral (fun x => ∑ k ∈ s, f k x) = ∑ k ∈ s, g.integral (f k) := by
  simp only [integral, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  exact g.chartIntegral_sum i s _ (fun k hk => (chartPartition i).continuous.mul (hf k hk))
    (fun k _ => tsupport_mul_subset_left.trans (chartPartition_support i))

lemma integral_nonneg [T2Space X] [CompactSpace X] (g : KaehlerMetric A)
    {f : X → ℝ} (hf : ∀ x, 0 ≤ f x) : 0 ≤ g.integral f := by
  apply Finset.sum_nonneg
  intro i _
  apply setIntegral_nonneg (A.chart i).open_target.measurableSet
  intro z hz
  exact mul_nonneg (mul_nonneg (chartPartition_nonneg i _) (hf _))
    (g.volumeCoefficient_pos i hz).le

end KaehlerMetric
end Anticanonical.SourceSmooth

end
end

end OAI
