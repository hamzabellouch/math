import OAI.Dynamics.StandardMap.VagueLimits

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped Topology ENNReal CompactlySupported Classical
namespace StandardMapEntropy
noncomputable instance : LocallyCompactSpace NonAffineArray := isClosed_affineLocus.isOpen_compl.locallyCompactSpace
noncomputable def nonaffinePart (μ : Measure DistanceArray) : Measure NonAffineArray := μ.comap Subtype.val
instance (μ : Measure DistanceArray) [IsFiniteMeasure μ] : IsFiniteMeasure (nonaffinePart μ) := inferInstanceAs (IsFiniteMeasure (μ.comap Subtype.val))
lemma integral_nonaffinePart_le (μ : Measure DistanceArray) [IsFiniteMeasure μ]
    (F : DistanceArray → ℝ) (hF : Continuous F) (hF0 : ∀ d,0≤F d) :
    (∫ d : NonAffineArray,F d.val ∂nonaffinePart μ)≤∫ d,F d ∂μ := by
  have he : (∫ d : NonAffineArray,F d.val ∂nonaffinePart μ)=∫ d in affineLocusᶜ,F d ∂μ := by
    convert! integral_subtype_comap isClosed_affineLocus.isOpen_compl.measurableSet F using 1
  rw [he]
  exact setIntegral_le_integral (hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (Filter.Eventually.of_forall hF0)
lemma integrable_nonaffinePart (μ : Measure DistanceArray) [IsFiniteMeasure μ]
    (F : DistanceArray → ℝ) (hF : Continuous F) : Integrable (fun d : NonAffineArray => F d.val) (nonaffinePart μ) := by
  have hi := (hF.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)).restrict (s := affineLocusᶜ)
  rw [← map_comap_subtype_coe isClosed_affineLocus.isOpen_compl.measurableSet,
    (MeasurableEmbedding.subtype_coe isClosed_affineLocus.isOpen_compl.measurableSet).integrable_map_iff] at hi
  exact hi
lemma compact_test_domination (g : C_c(NonAffineArray,ℝ)) :
    ∃ t : Finset ArrayTestIndex, ∃ C : ℝ, 0≤C ∧ ∀ d : NonAffineArray, |g d|≤C*∑ i∈t,arrayTest i d.val := by
  let F : Set DistanceArray := Subtype.val '' tsupport g
  have hF : IsCompact F := g.hasCompactSupport.isCompact.image continuous_subtype_val
  have hFa : F⊆affineLocusᶜ := by rintro d ⟨u,hu,rfl⟩; exact u.property
  obtain ⟨t,c,hc,hcover⟩ := compact_nonaffine_finite_tests F hF hFa
  obtain ⟨B,hB⟩ := g.hasCompactSupport.isCompact.exists_bound_of_continuousOn g.continuous.continuousOn
  let M : ℝ := max B 0
  have hM : 0≤M := le_max_right _ _
  refine ⟨t,M/c,div_nonneg hM hc.le,?_⟩
  intro d
  by_cases hd : d∈tsupport g
  · have h1 : |g d|≤M := by
      have hh : |g d|≤B := by convert! hB d hd using 1
      exact hh.trans (le_max_left _ _)
    have h2 := hcover d.val ⟨d,hd,rfl⟩
    have h3 := mul_le_mul_of_nonneg_left h2 (div_nonneg hM hc.le)
    rw [div_mul_cancel₀ M hc.ne'] at h3
    exact h1.trans h3
  · rw [image_eq_zero_of_notMem_tsupport hd,abs_zero]
    exact mul_nonneg (div_nonneg hM hc.le) (Finset.sum_nonneg (fun i hi => arrayTest_nonneg i d.val))
lemma cc_integral_nonaffine_bound (μ : Measure DistanceArray) [IsFiniteMeasure μ]
    (g : C_c(NonAffineArray,ℝ)) (t : Finset ArrayTestIndex) (C : ℝ) (hC : 0≤C)
    (hdom : ∀ d : NonAffineArray, |g d|≤C*∑ i∈t,arrayTest i d.val) :
    |∫ d,g d ∂nonaffinePart μ|≤C*∑ i∈t,∫ d,arrayTest i d ∂μ := by
  let F : DistanceArray → ℝ := fun d => ∑ i∈t,arrayTest i d
  have hF : Continuous F := continuous_finsetSum _ (fun i hi => continuous_arrayTest i)
  have hF0 : ∀ d,0≤F d := fun d => Finset.sum_nonneg (fun i hi => arrayTest_nonneg i d)
  have hiF := integrable_nonaffinePart μ F hF
  have hi := g.continuous.integrable_of_hasCompactSupport (μ := nonaffinePart μ) g.hasCompactSupport
  have h1 : |∫ d,g d ∂nonaffinePart μ|≤∫ d,|g d| ∂nonaffinePart μ := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := nonaffinePart μ) g
  have h2 : (∫ d,|g d| ∂nonaffinePart μ)≤C*(∫ d,F d.val ∂nonaffinePart μ) := by
    calc
      _ ≤ ∫ d,C*F d.val ∂nonaffinePart μ := integral_mono hi.abs (hiF.const_mul C) hdom
      _ = _ := integral_const_mul C _
  have h3 := integral_nonaffinePart_le μ F hF hF0
  apply (h1.trans h2).trans
  have he : (∫ d,F d ∂μ)=∑ i∈t,∫ d,arrayTest i d ∂μ := by
    apply integral_finsetSum
    intro i hi
    exact (continuous_arrayTest i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [← he]
  exact mul_le_mul_of_nonneg_left h3 hC
lemma exists_nonaffine_vague_limit {ι : Type*} (l : Ultrafilter ι) (μ : ι → Measure DistanceArray)
    [∀ i,IsFiniteMeasure (μ i)]
    (hb : ∀ j : ArrayTestIndex, ∃ C : ℝ, ∀ᶠ i in (l:Filter ι),(∫ d,arrayTest j d ∂μ i)≤C) :
    ∃ ν : Measure NonAffineArray, ν.Regular ∧ IsFiniteMeasureOnCompacts ν ∧ ∀ g : C_c(NonAffineArray,ℝ),
      Tendsto (fun i => ∫ d,g d ∂nonaffinePart (μ i)) (l:Filter ι) (𝓝 (∫ d,g d ∂ν)) := by
  apply exists_vague_limit
  intro g
  obtain ⟨t,C,hC,hdom⟩ := compact_test_domination g
  choose B hB using hb
  refine ⟨C*∑ j∈t,B j,?_⟩
  have hh : ∀ᶠ i in (l:Filter ι), ∀ j∈t,(∫ d,arrayTest j d ∂μ i)≤B j :=
    (eventually_all_finset t).mpr (fun j hj => hB j)
  filter_upwards [hh] with i hi
  exact (cc_integral_nonaffine_bound (μ i) g t C hC hdom).trans
    (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j hj => hi j hj)) hC)
end StandardMapEntropy

end OAI
