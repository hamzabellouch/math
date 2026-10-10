import OAI.Dynamics.ThreeTorus.PacketCalculus

namespace OAI

/-! Real perturbation, smooth cylinder approximation, tensor preparation, real packet families, and two neutral separations. -/

section

/-!
Concrete preparation with null zero sets for the packet ratios.
The perturbation parameter is REAL and works simultaneously for all packets.
No stage, spectral conclusion, or transport theorem is assumed here.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace ThreeTorus

/-- Apart from a Lebesgue null set of real parameters, a real perturbation
has no zero where the target coefficient is nonzero, up to the original measure.
This is the Fubini step in the manuscript, also for complex coefficients. -/
lemma real_perturbation_nonzero_ae {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] {F H : X → ℂ}
    (hF : Measurable F) (hH : Measurable H) :
    ∀ᵐ t : ℝ, ∀ᵐ x ∂μ, F x + (t : ℂ) * H x = 0 → H x = 0 := by
  have hm : MeasurableSet
      {p : X × ℝ | F p.1 + (p.2 : ℂ) * H p.1 = 0 → H p.1 = 0} := by
    apply MeasurableSet.imp
    · exact measurableSet_eq_fun ((hF.comp measurable_fst).add
        ((Complex.measurable_ofReal.comp measurable_snd).mul (hH.comp measurable_fst)))
        measurable_const
    · exact measurableSet_eq_fun (hH.comp measurable_fst) measurable_const
  apply (Measure.ae_ae_comm hm).1
  filter_upwards [] with x
  by_cases hx : H x = 0
  · exact Filter.Eventually.of_forall (fun _ _ => hx)
  · have hc : {t : ℝ | F x + (t : ℂ) * H x = 0}.Subsingleton := by
      intro t ht u hu
      apply Complex.ofReal_injective
      exact mul_right_cancel₀ hx (add_left_cancel (ht.trans hu.symm))
    have hz := hc.countable.measure_zero volume
    have hne : ∀ᵐ t : ℝ, F x + (t : ℂ) * H x ≠ 0 := by
      simpa only [ae_iff, not_not] using hz
    filter_upwards [hne] with t ht
    exact fun h => (ht h).elim

/-- The common real parameter avoids all the finite/countable list's bad fibers. -/
lemma real_perturbation_family_ae {X ι : Type*} [MeasurableSpace X] [Countable ι]
    (μ : Measure X) [SFinite μ] {F H : ι → X → ℂ}
    (hF : ∀ i, Measurable (F i)) (hH : ∀ i, Measurable (H i)) :
    ∀ᵐ t : ℝ, ∀ i, ∀ᵐ x ∂μ, F i x + (t : ℂ) * H i x = 0 → H i x = 0 := by
  rw [ae_all_iff]
  intro i
  exact real_perturbation_nonzero_ae μ (hF i) (hH i)

/-- The exact weighted zero-set integral asserted in the paper. -/
lemma real_perturbation_zero_set_integral {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] {F H : X → ℂ}
    (hF : Measurable F) (hH : Measurable H) :
    ∀ᵐ t : ℝ, ∫ x in {x | F x + (t : ℂ) * H x = 0}, ‖H x‖ ^ 2 ∂μ = 0 := by
  filter_upwards [real_perturbation_nonzero_ae μ hF hH] with t ht
  apply integral_eq_zero_of_ae
  change ∀ᵐ x ∂μ.restrict {x | F x + (t : ℂ) * H x = 0}, ‖H x‖ ^ 2 = 0
  apply (ae_restrict_iff' (measurableSet_eq_fun
    (hF.add (measurable_const.mul hH)) measurable_const)).2
  filter_upwards [ht] with x hx hmem
  simp [hx hmem]

/-- The parameter may be chosen positive and smaller than any prescribed tolerance,
simultaneously for a countable family of coefficient pairs. -/
lemma exists_small_real_perturbation {X ι : Type*} [MeasurableSpace X] [Countable ι]
    (μ : Measure X) [SFinite μ] {F H : ι → X → ℂ}
    (hF : ∀ i, Measurable (F i)) (hH : ∀ i, Measurable (H i))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t < ε ∧
      ∀ i, ∀ᵐ x ∂μ, F i x + (t : ℂ) * H i x = 0 → H i x = 0 := by
  have hvol : volume (Ioo (0 : ℝ) ε) ≠ 0 := by
    rw [Real.volume_Ioo, sub_zero]
    exact (ENNReal.ofReal_pos.mpr hε).ne'
  obtain ⟨t, ht, hgood⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hvol
    (ae_restrict_of_ae (real_perturbation_family_ae μ hF hH))
  exact ⟨t, ht.1, ht.2, hgood⟩

/-- The weighted coefficient measure in the constant-ratio preparation. -/
def coefficientMeasure {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (F : X → ℂ) : Measure X :=
  μ.withDensity (fun x => (‖F x‖₊ ^ 2 : ℝ≥0∞))

lemma ratio_mul_ae {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {F H : X → ℂ}
    (hzero : ∀ᵐ x ∂μ, F x = 0 → H x = 0) :
    (fun x => H x / F x * F x) =ᵐ[μ] H := by
  filter_upwards [hzero] with x hx
  by_cases h : F x = 0
  · simp [h, hx h]
  · exact div_mul_cancel₀ _ h

/-- Ratios are genuinely square integrable for the weighted measure; no
nonvanishing hypothesis on the source coefficient is imposed everywhere. -/
lemma ratio_memLp {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {F H : X → ℂ} (hF : Measurable F) (hH : Measurable H)
    (hH₂ : MemLp H 2 μ) (hzero : ∀ᵐ x ∂μ, F x = 0 → H x = 0) :
    MemLp (fun x => H x / F x) 2 (coefficientMeasure μ F) := by
  apply (memLp_two_iff_integrable_sq_norm (hH.div hF).aestronglyMeasurable).2
  change Integrable (fun x => ‖H x / F x‖ ^ 2)
    (μ.withDensity (fun x => ((‖F x‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞)))
  rw [integrable_withDensity_iff_integrable_smul (hF.nnnorm.pow_const 2)]
  apply hH₂.integrable_norm_pow (by norm_num) |>.congr
  filter_upwards [ratio_mul_ae hzero] with x hx
  have he := congrArg (fun z : ℂ => ‖z‖ ^ 2) hx
  simpa only [norm_mul, mul_pow, NNReal.smul_def, NNReal.coe_pow,
    coe_nnnorm, smul_eq_mul, mul_comm] using he.symm

/-- Exact weighted L² identity, as used before ratio truncation and rectangular
approximation in the manuscript. -/
lemma ratio_integral_sq {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {F H : X → ℂ} (hF : Measurable F)
    (hzero : ∀ᵐ x ∂μ, F x = 0 → H x = 0) :
    (∫ x, ‖H x / F x‖ ^ 2 ∂coefficientMeasure μ F) = ∫ x, ‖H x‖ ^ 2 ∂μ := by
  change (∫ x, ‖H x / F x‖ ^ 2
    ∂μ.withDensity (fun x => ((‖F x‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞))) = _
  rw [integral_withDensity_eq_integral_smul (hF.nnnorm.pow_const 2)]
  apply integral_congr_ae
  filter_upwards [ratio_mul_ae hzero] with x hx
  have he := congrArg (fun z : ℂ => ‖z‖ ^ 2) hx
  simpa only [norm_mul, mul_pow, NNReal.smul_def, NNReal.coe_pow,
    coe_nnnorm, smul_eq_mul, mul_comm] using he

end ThreeTorus
end
end

section

/-! Measurable ratio localization by actual disjoint smooth cylinder cutoffs.
Compact inner regularity replaces a particular rectangular grid; the retained
pieces are still finitely many disjoint compact subsets of the good cylinder. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology BigOperators
namespace ThreeTorus

lemma simple_compact_capture (ν : Measure (ℝ × UnitAddCircle)) [IsFiniteMeasure ν]
    [ν.InnerRegularCompactLTTop] (s : SimpleFunc (ℝ × UnitAddCircle) ℂ)
    {U : Set (ℝ × UnitAddCircle)} (hU : IsOpen U) (hν : ν Uᶜ = 0)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K : ↥s.range → Set (ℝ × UnitAddCircle),
      (∀ i, IsCompact (K i) ∧ K i ⊆ U ∩ s ⁻¹' {i.val}) ∧
      Pairwise (Disjoint on K) ∧ ν (⋃ i, K i)ᶜ < ε := by
  classical
  let I := ↥s.range
  obtain ⟨δ,hδ,hδε⟩ := ENNReal.exists_pos_mul_lt (a := (Fintype.card I : ℝ≥0∞))
    (by finiteness) hε
  have he (i : I) := (hU.measurableSet.inter (s.measurableSet_preimage {i.val})).exists_isCompact_sdiff_lt
    (μ := ν) (measure_ne_top _ _) hδ.ne'
  choose K hKU hK hdiff using he
  refine ⟨K,fun i => ⟨hK i,hKU i⟩,?_,?_⟩
  · intro i j hij
    change Disjoint (K i) (K j)
    rw [Set.disjoint_left]
    intro x hxi hxj
    apply hij
    apply Subtype.ext
    exact (hKU i hxi).2.symm.trans (hKU j hxj).2
  · have hsub : (⋃ i, K i)ᶜ ⊆ Uᶜ ∪ ⋃ i : I, (U ∩ s ⁻¹' {i.val}) \ K i := by
      intro x hx
      by_cases hxU : x ∈ U
      · right
        let i : I := ⟨s x,s.mem_range_self x⟩
        exact mem_iUnion.mpr ⟨i,⟨⟨hxU,rfl⟩,fun h => hx (mem_iUnion.mpr ⟨i,h⟩)⟩⟩
      · exact Or.inl hxU
    calc
      ν (⋃ i, K i)ᶜ ≤ ν (Uᶜ ∪ ⋃ i : I, (U ∩ s ⁻¹' {i.val}) \ K i) := measure_mono hsub
      _ ≤ ν Uᶜ + ν (⋃ i : I, (U ∩ s ⁻¹' {i.val}) \ K i) := measure_union_le _ _
      _ = ν (⋃ i : I, (U ∩ s ⁻¹' {i.val}) \ K i) := by rw [hν,zero_add]
      _ ≤ ∑ i : I, ν ((U ∩ s ⁻¹' {i.val}) \ K i) := by
        simpa only [tsum_fintype] using measure_iUnion_le (fun i : I => (U ∩ s ⁻¹' {i.val}) \ K i)
      _ ≤ ∑ _i : I, δ := Finset.sum_le_sum (fun i _ => (hdiff i).le)
      _ = δ * (Fintype.card I : ℝ≥0∞) := by simp [mul_comm]
      _ < ε := hδε

lemma disjoint_cutoffs_value {ι : Type*} [Fintype ι]
    {K : ι → Set (ℝ × UnitAddCircle)} {χ : ι → ℝ × UnitAddCircle → ℝ}
    (hχ : ∀ i x, x ∈ K i → χ i x = 1)
    (hd : Pairwise (fun i j => Disjoint (tsupport (χ i)) (tsupport (χ j))))
    {i : ι} {x : ℝ × UnitAddCircle} (hx : x ∈ K i) :
    χ i x = 1 ∧ ∀ j, j ≠ i → χ j x = 0 := by
  refine ⟨hχ i x hx,fun j hji => ?_⟩
  by_contra hj
  have hi : x ∈ tsupport (χ i) := subset_tsupport _ (by change χ i x ≠ 0; rw [hχ i x hx]; exact one_ne_zero)
  exact Set.disjoint_left.1 (hd hji) (subset_tsupport _ hj) hi

/-- Smooth disjoint bump representation agrees with a prescribed simple
function off a set of arbitrarily small measure. It also recovers the
untagged constant one there. Zero simple values are retained as colors. -/
theorem simple_smooth_disjoint_capture (ν : Measure (ℝ × UnitAddCircle)) [IsFiniteMeasure ν]
    [ν.InnerRegularCompactLTTop] (s : SimpleFunc (ℝ × UnitAddCircle) ℂ)
    {U : Set (ℝ × UnitAddCircle)} (hU : IsOpen U) (hν : ν Uᶜ = 0)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ χ : ↥s.range → ℝ × UnitAddCircle → ℝ,
      (∀ i, CylinderSmooth (χ i) ∧ HasCompactSupport (χ i) ∧ tsupport (χ i) ⊆ U ∧
        ∀ x, 0 ≤ χ i x ∧ χ i x ≤ 1) ∧
      Pairwise (fun i j => Disjoint (tsupport (χ i)) (tsupport (χ j))) ∧
      ∃ Z : Set (ℝ × UnitAddCircle), MeasurableSet Z ∧ ν Z < ε ∧
        ∀ x ∉ Z, (∑ i, χ i x) = 1 ∧ (∑ i, i.val * (χ i x:ℂ)) = s x := by
  classical
  obtain ⟨K,hK,hd,hεK⟩ := simple_compact_capture ν s hU hν hε
  obtain ⟨χ,hχ,hdχ⟩ := finite_disjoint_cylinder_cutoffs K (fun _ => U)
    (fun i => (hK i).1) (fun _ => hU) (fun i => (hK i).2.trans inter_subset_left) hd
  refine ⟨χ,fun i => ⟨(hχ i).1,(hχ i).2.1,(hχ i).2.2.1,(hχ i).2.2.2.1⟩,
    hdχ,(⋃ i, K i)ᶜ,(isClosed_iUnion_of_finite (fun i => (hK i).1.isClosed)).measurableSet.compl,
    hεK,?_⟩
  intro x hx
  have hx' : x ∈ ⋃ i, K i := not_not.mp hx
  obtain ⟨i,hi⟩ := mem_iUnion.mp hx'
  have hh := disjoint_cutoffs_value (fun r y hy => ((hχ r).2.2.2.2 y hy).self_of_nhds) hdχ hi
  have hs : s x = i.val := (hK i).2 hi |>.2
  constructor
  · rw [Finset.sum_eq_single i]
    · exact hh.1
    · intro j _ hj; exact hh.2 j hj
    · simp
  · rw [Finset.sum_eq_single i]
    · rw [hh.1,Complex.ofReal_one,mul_one,hs]
    · intro j _ hj; rw [hh.2 j hj,Complex.ofReal_zero,mul_zero]
    · simp

end ThreeTorus
end
end

section

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace ThreeTorus

/-- A bounded error supported on a sufficiently small set has small L² norm.
The bound is selected before the exceptional set/cutoffs are selected. -/
lemma exists_measure_bound_eLpNorm_lt {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] (μ : Measure X) {B : ℝ} (hB : 0 ≤ B)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ (Z : Set X), MeasurableSet Z → μ Z < δ →
      ∀ f : X → E, AEStronglyMeasurable f μ →
        (∀ x, ‖f x‖ ≤ B) → (∀ x ∉ Z, f x = 0) → eLpNorm f 2 μ < ε := by
  obtain ⟨c,hc,hcε⟩ := ENNReal.exists_pos_mul_lt (a := ‖B‖ₑ) (by finiteness) hε
  refine ⟨c^2,by positivity,fun Z hZ hμ f hfm hf hz => ?_⟩
  have hmono : eLpNorm f 2 μ ≤ eLpNorm (Z.indicator (fun _ : X => B)) 2 μ := by
    apply eLpNorm_mono hfm
    intro x
    by_cases hx : x ∈ Z
    · simpa [Set.indicator_of_mem hx,Real.norm_eq_abs,abs_of_nonneg hB] using hf x
    · simp [Set.indicator_of_notMem hx,hz x hx]
  have hr : (c^2) ^ (1/(2:ℝ)) = c := by
    rw [← ENNReal.rpow_natCast,← ENNReal.rpow_mul]
    norm_num
  calc
    eLpNorm f 2 μ ≤ eLpNorm (Z.indicator (fun _ : X => B)) 2 μ := hmono
    _ = ‖B‖ₑ * μ Z ^ (1/(2:ℝ)) := by
      rw [eLpNorm_indicator_const hZ.nullMeasurableSet (by norm_num) (by norm_num)]
      norm_num
    _ ≤ ‖B‖ₑ * (c^2) ^ (1/(2:ℝ)) := mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hμ.le (by positivity))
    _ = c * ‖B‖ₑ := by rw [hr,mul_comm]
    _ < ε := hcε

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology BigOperators
namespace ThreeTorus

/-- Weighted simultaneous approximation of the untagged vector and its
measurable ratio. The finite constants are fixed before the interior trimming;
zero constants are not discarded. -/
theorem weighted_smooth_disjoint_approx (ν : Measure (ℝ × UnitAddCircle)) [IsFiniteMeasure ν]
    [ν.InnerRegularCompactLTTop] {R : ℝ × UnitAddCircle → ℂ} (hR : MemLp R 2 ν)
    {U : Set (ℝ × UnitAddCircle)} (hU : IsOpen U) (hν : ν Uᶜ = 0)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ s : SimpleFunc (ℝ × UnitAddCircle) ℂ,
    ∃ χ : ↥s.range → ℝ × UnitAddCircle → ℝ,
      (∀ i, CylinderSmooth (χ i) ∧ HasCompactSupport (χ i) ∧ tsupport (χ i) ⊆ U ∧
        ∀ x, 0 ≤ χ i x ∧ χ i x ≤ 1) ∧
      Pairwise (fun i j => Disjoint (tsupport (χ i)) (tsupport (χ j))) ∧
      eLpNorm (fun x => (1:ℂ) - ∑ i, (χ i x:ℂ)) 2 ν < ε ∧
      eLpNorm (fun x => R x - ∑ i, i.val * (χ i x:ℂ)) 2 ν < ε := by
  classical
  have hε2 : ε / 2 ≠ 0 := ENNReal.div_ne_zero.mpr ⟨hε,by norm_num⟩
  obtain ⟨s,hs,_⟩ := hR.exists_simpleFunc_eLpNorm_sub_lt (by norm_num) hε2
  let I := ↥s.range
  let B : ℝ := 1 + Fintype.card I + 2 * ∑ i : I, ‖i.val‖
  have hB : 0 ≤ B := by dsimp [B]; positivity
  obtain ⟨δ,hδ,hsmall⟩ := exists_measure_bound_eLpNorm_lt (E := ℂ) ν hB hε2
  obtain ⟨χ,hχ,hd,Z,hZ,hZδ,heq⟩ := simple_smooth_disjoint_capture ν s hU hν hδ.ne'
  have hnχ (i : I) (x : ℝ × UnitAddCircle) : ‖(χ i x:ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ((hχ i).2.2.2 x).1]
      using ((hχ i).2.2.2 x).2
  have hnχsum (x : ℝ × UnitAddCircle) : ‖∑ i : I, (χ i x:ℂ)‖ ≤ Fintype.card I := calc
    _ ≤ ∑ i : I, ‖(χ i x:ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : I, (1:ℝ) := Finset.sum_le_sum (fun i _ => hnχ i x)
    _ = _ := by simp
  have hntagsum (x : ℝ × UnitAddCircle) : ‖∑ i : I, i.val * (χ i x:ℂ)‖ ≤ ∑ i : I, ‖i.val‖ := calc
    _ ≤ ∑ i : I, ‖i.val * (χ i x:ℂ)‖ := norm_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum (fun i _ => by rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (hnχ i x))
  have hns (x : ℝ × UnitAddCircle) : ‖s x‖ ≤ ∑ i : I, ‖i.val‖ := by
    let i : I := ⟨s x,s.mem_range_self x⟩
    exact Finset.single_le_sum (fun j _ => norm_nonneg j.val) (Finset.mem_univ i)
  have hu : eLpNorm (fun x => (1:ℂ) - ∑ i, (χ i x:ℂ)) 2 ν < ε/2 := by
    apply hsmall Z hZ hZδ
    · apply Continuous.aestronglyMeasurable
      exact continuous_const.sub (continuous_finsetSum _ (fun i _ =>
        Complex.continuous_ofReal.comp (hχ i).1.continuous))
    · intro x
      have hh := norm_sub_le (1:ℂ) (∑ i : I, (χ i x:ℂ))
      rw [norm_one] at hh
      change ‖(1:ℂ) - ∑ i : I, (χ i x:ℂ)‖ ≤ 1 + Fintype.card I + 2 * ∑ i : I, ‖i.val‖
      have hp : 0 ≤ ∑ i : I, ‖i.val‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
      linarith [hnχsum x]
    · intro x hx
      rw [sub_eq_zero]
      have hh := congrArg (fun t : ℝ => (t:ℂ)) (heq x hx).1
      simpa using hh.symm
  have ht : eLpNorm (fun x => s x - ∑ i, i.val * (χ i x:ℂ)) 2 ν < ε/2 := by
    apply hsmall Z hZ hZδ
    · apply s.measurable.aestronglyMeasurable.sub
      apply Continuous.aestronglyMeasurable
      exact continuous_finsetSum _ (fun i _ =>
        continuous_const.mul (Complex.continuous_ofReal.comp (hχ i).1.continuous))
    · intro x
      have hh := norm_sub_le (s x) (∑ i : I, i.val * (χ i x:ℂ))
      have hc : (0:ℝ) ≤ Fintype.card I := Nat.cast_nonneg _
      change ‖s x - ∑ i : I, i.val * (χ i x:ℂ)‖ ≤ 1 + Fintype.card I + 2 * ∑ i : I, ‖i.val‖
      linarith [hns x,hntagsum x]
    · intro x hx
      exact sub_eq_zero.mpr ((heq x hx).2.symm)
  refine ⟨s,χ,hχ,hd,hu.trans_le (by simpa only [ENNReal.add_halves] using (le_self_add : ε/2 ≤ ε/2+ε/2)),?_⟩
  calc
    eLpNorm (fun x => R x - ∑ i, i.val * (χ i x:ℂ)) 2 ν =
      eLpNorm ((R - ⇑s) + (fun x => s x - ∑ i, i.val * (χ i x:ℂ))) 2 ν := by
        congr 1; funext x; simp
    _ ≤ eLpNorm (R-⇑s) 2 ν + eLpNorm (fun x => s x - ∑ i, i.val * (χ i x:ℂ)) 2 ν :=
      eLpNorm_add_le (by norm_num)
    _ < ε/2 + ε/2 := ENNReal.add_lt_add hs ht
    _ = ε := ENNReal.add_halves ε

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology BigOperators
namespace ThreeTorus

lemma eLpNorm_coefficientMeasure {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {F g : X → ℂ} (hF : Measurable F) (hg : Measurable g) :
    eLpNorm g 2 (coefficientMeasure μ F) = eLpNorm (fun x => g x * F x) 2 μ := by
  change eLpNorm g 2 (coefficientMeasure μ F) = eLpNorm (g * F) 2 μ
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2:ℝ≥0∞) ≠ 0)
    (by norm_num : (2:ℝ≥0∞) ≠ ∞) hg.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2:ℝ≥0∞) ≠ 0)
    (by norm_num : (2:ℝ≥0∞) ≠ ∞) (hg.mul hF).aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat]
  congr 1
  change (∫⁻ x, ‖g x‖ₑ ^ (2:ℝ) ∂μ.withDensity (fun x => (‖F x‖₊ ^ 2:ℝ≥0∞))) = _
  rw [lintegral_withDensity_eq_lintegral_mul μ (hF.nnnorm.coe_nnreal_ennreal.pow_const 2)
    (hg.enorm.pow_const _)]
  apply lintegral_congr
  intro x
  simp [Pi.mul_apply,mul_pow,enorm_eq_nnnorm,mul_comm]

lemma finite_coefficientMeasure {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {F : X → ℂ} (hF : MemLp F 2 μ) : IsFiniteMeasure (coefficientMeasure μ F) := by
  apply isFiniteMeasure_withDensity
  have hf := (hasFiniteIntegral_iff_norm _).1
    (hF.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).hasFiniteIntegral
  simpa only [Real.norm_eq_abs,abs_pow,abs_norm,ENNReal.ofReal_pow (norm_nonneg _),
    ofReal_norm,enorm_eq_nnnorm,ENNReal.coe_pow] using hf.ne

/-- The literal coefficient errors after constant-ratio trimming, not just
errors of the ratios in an auxiliary weighted space. -/
theorem coefficient_smooth_disjoint_approx (μ : Measure (ℝ × UnitAddCircle))
    {F H : ℝ × UnitAddCircle → ℂ} (hFm : Measurable F) (hHm : Measurable H)
    (hF : MemLp F 2 μ) (hH : MemLp H 2 μ)
    (hzero : ∀ᵐ x ∂μ, F x = 0 → H x = 0)
    {U : Set (ℝ × UnitAddCircle)} (hU : IsOpen U)
    (hsupp : ∀ᵐ x ∂μ, x ∉ U → F x = 0) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ s : SimpleFunc (ℝ × UnitAddCircle) ℂ,
    ∃ χ : ↥s.range → ℝ × UnitAddCircle → ℝ,
      (∀ i, CylinderSmooth (χ i) ∧ HasCompactSupport (χ i) ∧ tsupport (χ i) ⊆ U ∧
        ∀ x, 0 ≤ χ i x ∧ χ i x ≤ 1) ∧
      Pairwise (fun i j => Disjoint (tsupport (χ i)) (tsupport (χ j))) ∧
      eLpNorm (fun x => F x - ∑ i, (χ i x:ℂ)*F x) 2 μ < ε ∧
      eLpNorm (fun x => H x - ∑ i, i.val * ((χ i x:ℂ)*F x)) 2 μ < ε := by
  let := finite_coefficientMeasure hF
  have hν : coefficientMeasure μ F Uᶜ = 0 := by
    rw [coefficientMeasure,withDensity_apply _ hU.measurableSet.compl]
    calc
      _ = ∫⁻ x, (0 : ℝ≥0∞) ∂μ.restrict Uᶜ := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_of_ae hsupp,ae_restrict_mem hU.measurableSet.compl] with x hx hxu
        simp [hx hxu]
      _ = 0 := lintegral_zero
  have hR := ratio_memLp hFm hHm hH hzero
  obtain ⟨s,χ,hχ,hd,hu,ht⟩ := weighted_smooth_disjoint_approx (coefficientMeasure μ F) hR hU hν hε
  have hc : ∀ i, Measurable (fun x => (χ i x:ℂ)) := fun i =>
    Complex.measurable_ofReal.comp (hχ i).1.continuous.measurable
  have hsum : Measurable (fun x => ∑ i, (χ i x:ℂ)) := Finset.measurable_sum _ (fun i _ => hc i)
  have htsum : Measurable (fun x => ∑ i, i.val * (χ i x:ℂ)) :=
    Finset.measurable_sum _ (fun i _ => measurable_const.mul (hc i))
  rw [eLpNorm_coefficientMeasure (g := fun x => (1 : ℂ) - ∑ i, (χ i x:ℂ)) hFm (measurable_const.sub hsum)] at hu
  rw [eLpNorm_coefficientMeasure (g := fun x => H x / F x - ∑ i, i.val * (χ i x:ℂ)) hFm ((hHm.div hFm).sub htsum)] at ht
  refine ⟨s,χ,hχ,hd,?_,?_⟩
  · convert hu using 1
    congr 1; funext x
    simp only [sub_mul,one_mul,Finset.sum_mul]
  · rw [← eLpNorm_congr_ae (show (fun x => (H x/F x - ∑ i, i.val*(χ i x:ℂ))*F x) =ᵐ[μ]
      (fun x => H x - ∑ i, i.val*((χ i x:ℂ)*F x)) from ?_)]
    · exact ht
    · filter_upwards [ratio_mul_ae hzero] with x hx
      simp only [sub_mul,hx,Finset.sum_mul,mul_assoc]

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
namespace ThreeTorus

/-- Fundamental cylinder with the exact normalized slow-coordinate measure. -/
def cylinderVolume (o : ℝ) : Measure (ℝ × UnitAddCircle) :=
  (volume.restrict (Ioc o (o+1))).prod phaseHaar

def cylinderToSlow (p : ℝ × UnitAddCircle) : UnitAddCircle × UnitAddCircle := (p.1,p.2)

def slowToCylinder (o : ℝ) (p : UnitAddCircle × UnitAddCircle) : ℝ × UnitAddCircle :=
  (circleRep o p.1,p.2)

lemma measurePreserving_cylinderToSlow (o : ℝ) :
    MeasurePreserving cylinderToSlow (cylinderVolume o) slowVolume := by
  have h : MeasurePreserving (fun x : ℝ => (x : UnitAddCircle))
      (volume.restrict (Ioc o (o+1))) phaseHaar := by
    simpa [phaseHaar,AddCircle.volume_eq_smul_haarAddCircle] using AddCircle.measurePreserving_mk 1 o
  exact h.prod (MeasurePreserving.id phaseHaar)

lemma measurable_slowToCylinder (o : ℝ) : Measurable (slowToCylinder o) :=
  ((measurable_circleRep o).comp measurable_fst).prodMk measurable_snd

lemma cylinderToSlow_slowToCylinder (o : ℝ) (p : UnitAddCircle × UnitAddCircle) :
    cylinderToSlow (slowToCylinder o p) = p := by
  simp [cylinderToSlow,slowToCylinder,coe_circleRep]

lemma slowToCylinder_cylinderToSlow (o : ℝ) :
    (slowToCylinder o ∘ cylinderToSlow) =ᵐ[cylinderVolume o] id := by
  have hh : ∀ᵐ x ∂volume.restrict (Ioc o (o+1)), x ∈ Ioc o (o+1) :=
    ae_restrict_mem measurableSet_Ioc
  have hm : ∀ᵐ p ∂cylinderVolume o, p.1 ∈ Ioc o (o+1) :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_Ioc.preimage measurable_fst)).2
      (hh.mono (fun x hx => Filter.Eventually.of_forall (fun _y : UnitAddCircle => hx)))
  filter_upwards [hm] with x hx
  simp only [Function.comp_apply,cylinderToSlow,slowToCylinder,id_eq]
  congr 1
  exact circleRep_coe hx

lemma measurePreserving_slowToCylinder (o : ℝ) :
    MeasurePreserving (slowToCylinder o) slowVolume (cylinderVolume o) := by
  refine ⟨measurable_slowToCylinder o,?_⟩
  rw [← (measurePreserving_cylinderToSlow o).map_eq,
    Measure.map_map (measurable_slowToCylinder o) (measurePreserving_cylinderToSlow o).measurable,
    Measure.map_congr (slowToCylinder_cylinderToSlow o),Measure.map_id]

instance (o : ℝ) : IsProbabilityMeasure (cylinderVolume o) := by
  rw [← (measurePreserving_slowToCylinder o).map_eq]
  infer_instance

lemma eLpNorm_cylinder_pull (o : ℝ) (f : UnitAddCircle × UnitAddCircle → ℂ)
    (hf : AEStronglyMeasurable f slowVolume) :
    eLpNorm (f ∘ cylinderToSlow) 2 (cylinderVolume o) = eLpNorm f 2 slowVolume :=
  eLpNorm_comp_measurePreserving hf (measurePreserving_cylinderToSlow o)

lemma eLpNorm_slow_pull (o : ℝ) (f : ℝ × UnitAddCircle → ℂ)
    (hf : AEStronglyMeasurable f (cylinderVolume o)) :
    eLpNorm (f ∘ slowToCylinder o) 2 slowVolume = eLpNorm f 2 (cylinderVolume o) :=
  eLpNorm_comp_measurePreserving hf (measurePreserving_slowToCylinder o)

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace ThreeTorus

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {d : Type*} [Fintype d]

def multiTrigPolynomial (c : (d → ℤ) →₀ ℂ) : C(UnitAddTorus d,ℂ) :=
  c.sum (fun k a => a • UnitAddTorus.mFourier k)

lemma multiTrigPolynomial_apply (c : (d → ℤ) →₀ ℂ) (x : UnitAddTorus d) :
    multiTrigPolynomial c x = ∑ k ∈ c.support, c k * UnitAddTorus.mFourier k x := by
  simp [multiTrigPolynomial,Finsupp.sum]

lemma mFourier_smooth_lift (k : d → ℤ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : d → ℝ => UnitAddTorus.mFourier k (fun i => (x i : UnitAddCircle))) := by
  change ContDiff ℝ _ (fun x : d → ℝ => ∏ i, fourier (k i) (x i : UnitAddCircle))
  apply contDiff_prod
  intro i _
  simp only [fourier_coe_apply,Complex.ofReal_one,div_one]
  exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ i))).cexp

lemma multiTrigPolynomial_smooth_lift (c : (d → ℤ) →₀ ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : d → ℝ => multiTrigPolynomial c (fun i => (x i : UnitAddCircle))) := by
  simp_rw [multiTrigPolynomial_apply]
  exact ContDiff.sum (fun k _ => contDiff_const.mul (mFourier_smooth_lift k))

/-- The exact existing multivariate Fourier basis supplies smooth finite
polynomials in the FULL torus space, not just a cyclic subspace. -/
theorem exists_L2_multiTrig {f : UnitAddTorus d → ℂ} (hf : MemLp f 2 volume)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ c : (d → ℤ) →₀ ℂ,
      eLpNorm (fun x => f x-multiTrigPolynomial c x) 2 volume < ENNReal.ofReal ε := by
  classical
  have hd : hf.toLp f ∈ ((Submodule.span ℂ (range (UnitAddTorus.mFourierLp (d := d) 2))).topologicalClosure : Set (Lp ℂ 2 (volume : Measure (UnitAddTorus d)))) := by
    rw [UnitAddTorus.span_mFourierLp_closure_eq_top (by norm_num : (2:ℝ≥0∞) ≠ ∞)]
    trivial
  change hf.toLp f ∈ closure (Submodule.span ℂ (range (UnitAddTorus.mFourierLp (d := d) 2)) : Set (Lp ℂ 2 (volume : Measure (UnitAddTorus d)))) at hd
  obtain ⟨g,hg,hfg⟩ := Metric.mem_closure_iff.1 hd ε hε
  obtain ⟨c,hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hg
  have he : ContinuousMap.toLp (E := ℂ) 2 volume ℂ (multiTrigPolynomial c) = g := by
    rw [← hc,multiTrigPolynomial]
    simp [Finsupp.sum]
  have hae : (fun x => f x-multiTrigPolynomial c x) =ᵐ[volume] (fun x => (hf.toLp f-g) x) := by
    filter_upwards [hf.coeFn_toLp,ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume (multiTrigPolynomial c),
      Lp.coeFn_sub (hf.toLp f) g] with x hx hy hz
    rw [he] at hy
    simp only [hz,Pi.sub_apply,hx,hy]
  refine ⟨c,?_⟩
  rw [eLpNorm_congr_ae hae,← Lp.enorm_def,← ofReal_norm]
  apply (ENNReal.ofReal_lt_ofReal_iff hε).mpr
  simpa only [dist_eq_norm] using hfg

lemma exists_uniform_multiTrig {f : UnitAddTorus d → ℂ} (hf : Continuous f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ c : (d → ℤ) →₀ ℂ, ∀ x, ‖f x-multiTrigPolynomial c x‖ < ε := by
  let F : C(UnitAddTorus d,ℂ) := ⟨f,hf⟩
  have hd : F ∈ (Submodule.span ℂ (range (UnitAddTorus.mFourier (d := d)))).topologicalClosure := by
    rw [UnitAddTorus.span_mFourier_closure_eq_top]
    trivial
  change F ∈ closure (Submodule.span ℂ (range (UnitAddTorus.mFourier (d := d))) : Set C(UnitAddTorus d,ℂ)) at hd
  obtain ⟨g,hg,hfg⟩ := Metric.mem_closure_iff.1 hd ε hε
  obtain ⟨c,hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hg
  refine ⟨c,?_⟩
  intro x
  have he : multiTrigPolynomial c = g := hc
  rw [he]
  exact (ContinuousMap.norm_coe_le_norm (F-g) x).trans_lt (by simpa only [dist_eq_norm] using hfg)

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace ThreeTorus

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def slowPair : UnitAddTorus (Fin 2) ≃ᵐ (UnitAddCircle × UnitAddCircle) :=
  MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle)

lemma slowPair_symm_apply (p : UnitAddCircle × UnitAddCircle) : slowPair.symm p = ![p.1,p.2] := rfl

lemma continuous_slowPair_symm : Continuous slowPair.symm := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_fst
  · exact continuous_snd

lemma measurePreserving_slowPair : MeasurePreserving slowPair volume slowVolume :=
  measurePreserving_piFinTwo (fun _ : Fin 2 => phaseHaar)

/-- Arbitrary actual L² coefficients admit smooth periodic approximation in
both slow variables. Density is in the full two-torus L² space. -/
lemma exists_smooth_slow_approx {f : UnitAddCircle × UnitAddCircle → ℂ}
    (hf : MemLp f 2 slowVolume) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : UnitAddCircle × UnitAddCircle → ℂ, Continuous g ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => g (p.1,p.2)) ∧
      eLpNorm (fun p => f p-g p) 2 slowVolume < ENNReal.ofReal ε := by
  obtain ⟨c,hc⟩ := exists_L2_multiTrig (hf.comp_measurePreserving measurePreserving_slowPair) hε
  let g : UnitAddCircle × UnitAddCircle → ℂ := multiTrigPolynomial c ∘ slowPair.symm
  have hgc : Continuous g := (multiTrigPolynomial c).continuous.comp continuous_slowPair_symm
  refine ⟨g,hgc,?_,?_⟩
  · have hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => ![p.1,p.2]) := by
      apply contDiff_pi.mpr
      intro i
      fin_cases i
      · exact contDiff_fst
      · exact contDiff_snd
    have he : (fun p : ℝ × ℝ => g (p.1,p.2)) =
        (fun x : Fin 2 → ℝ => multiTrigPolynomial c (fun i => (x i : UnitAddCircle))) ∘
          (fun p : ℝ × ℝ => ![p.1,p.2]) := by
      funext p
      change multiTrigPolynomial c (slowPair.symm ((p.1:UnitAddCircle),(p.2:UnitAddCircle))) = _
      apply congrArg (multiTrigPolynomial c)
      ext i
      fin_cases i <;> rfl
    rw [he]
    exact (multiTrigPolynomial_smooth_lift c).comp hd
  · have he : (fun p => f p-g p) ∘ slowPair =
        fun x => (f ∘ slowPair) x-multiTrigPolynomial c x := by
      funext x
      simp [g,Function.comp_def]
    have heq := eLpNorm_comp_measurePreserving
      (g := fun p => f p-g p) (p := 2)
      (hf.aestronglyMeasurable.sub hgc.aestronglyMeasurable) measurePreserving_slowPair
    rw [he] at heq
    exact heq ▸ hc

lemma circleRep_mem (o : ℝ) (u : UnitAddCircle) : circleRep o u ∈ Ioc o (o+1) :=
  ((AddCircle.measurableEquivIoc 1 o) u).property

lemma cylinderTorusCutoff_rep {χ : ℝ × UnitAddCircle → ℝ} {o : ℝ}
    (hs : support χ ⊆ Ioo o (o+1) ×ˢ univ) (p : UnitAddCircle × UnitAddCircle) :
    cylinderTorusCutoff χ p = χ (circleRep o p.1,p.2) := by
  have hh := cylinderTorusCutoff_eq hs (circleRep_mem o p.1) p.2
  simpa only [coe_circleRep] using hh

lemma cylinderTorusCutoff_bounds {χ : ℝ × UnitAddCircle → ℝ} {o : ℝ}
    (hs : support χ ⊆ Ioo o (o+1) ×ˢ univ) (hb : ∀ p, 0 ≤ χ p ∧ χ p ≤ 1)
    (p : UnitAddCircle × UnitAddCircle) :
    0 ≤ cylinderTorusCutoff χ p ∧ cylinderTorusCutoff χ p ≤ 1 := by
  rw [cylinderTorusCutoff_rep hs p]
  exact hb _

lemma cylinderTorusCutoff_fixes {χ : ℝ × UnitAddCircle → ℝ} {o l u : ℝ}
    (hs : support χ ⊆ Ioo o (o+1) ×ˢ univ) (hol : o < l) (huo : u < o+1)
    (hχ : ∀ p ∈ Icc l u ×ˢ univ, χ p = 1)
    {f : UnitAddCircle × UnitAddCircle → ℂ}
    (hf : support f ⊆ ((fun x : ℝ => (x:UnitAddCircle)) '' Icc l u) ×ˢ univ) (p) :
    (cylinderTorusCutoff χ p:ℂ)*f p = f p := by
  by_cases hz : f p = 0
  · simp [hz]
  obtain ⟨x,hx,hxp⟩ := (hf hz).1
  have hxI : x ∈ Ioc o (o+1) := ⟨hol.trans_le hx.1,hx.2.trans huo.le⟩
  have he : p = ((x:UnitAddCircle),p.2) := Prod.ext hxp.symm rfl
  rw [he,cylinderTorusCutoff_eq hs hxI p.2,hχ _ ⟨hx,mem_univ _⟩]
  simp

/-- The same smooth compact cutoff preserves the supported old coefficient,
and smooths without any extra approximation loss. -/
lemma exists_supported_slow_approx {f : UnitAddCircle × UnitAddCircle → ℂ}
    (hf : MemLp f 2 slowVolume) {χ : ℝ × UnitAddCircle → ℝ} {o l u : ℝ}
    (hχs : CylinderSmooth χ) (hχc : HasCompactSupport χ)
    (hχsupp : support χ ⊆ Ioo o (o+1) ×ˢ univ)
    (hχb : ∀ p, 0 ≤ χ p ∧ χ p ≤ 1) (hol : o < l) (huo : u < o+1)
    (hχ1 : ∀ p ∈ Icc l u ×ˢ univ, χ p = 1)
    (hfs : support f ⊆ ((fun x : ℝ => (x:UnitAddCircle)) '' Icc l u) ×ˢ univ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : UnitAddCircle × UnitAddCircle → ℂ, Continuous g ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => g (p.1,p.2)) ∧
      eLpNorm (fun p => f p-(cylinderTorusCutoff χ p:ℂ)*g p) 2 slowVolume < ENNReal.ofReal ε := by
  obtain ⟨g,hgc,hgs,hg⟩ := exists_smooth_slow_approx hf hε
  have hmeas : AEStronglyMeasurable
      (fun p => f p-(cylinderTorusCutoff χ p:ℂ)*g p) slowVolume :=
    hf.aestronglyMeasurable.sub
      ((Complex.continuous_ofReal.comp (cylinderTorusCutoff_continuous hχs hχc)).mul
        hgc).aestronglyMeasurable
  refine ⟨g,hgc,hgs,lt_of_le_of_lt (eLpNorm_mono hmeas ?_) hg⟩
  intro p
  have he := cylinderTorusCutoff_fixes hχsupp hol huo hχ1 hfs p
  have hb := cylinderTorusCutoff_bounds hχsupp hχb p
  calc
    ‖f p-(cylinderTorusCutoff χ p:ℂ)*g p‖ =
        ‖(cylinderTorusCutoff χ p:ℂ)*(f p-g p)‖ := by rw [mul_sub,he]
    _ ≤ ‖f p-g p‖ := by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hb.1]
      exact mul_le_of_le_one_left (norm_nonneg _) hb.2

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate ENNReal
namespace ThreeTorus

lemma cylinder_mem_open_ae (o : ℝ) :
    ∀ᵐ p ∂cylinderVolume o, p ∈ Ioo o (o+1) ×ˢ (univ : Set UnitAddCircle) := by
  have hh : ∀ᵐ x ∂volume.restrict (Ioc o (o+1)), x ∈ Ioo o (o+1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae (volume.ae_ne (o+1))] with x hx hn
    exact ⟨hx.1,lt_of_le_of_ne hx.2 hn⟩
  apply (Measure.ae_prod_iff_ae_ae (isOpen_Ioo.prod isOpen_univ).measurableSet).2
  filter_upwards [hh] with x hx
  exact .of_forall fun _ => ⟨hx,mem_univ _⟩

/-- Actual torus coefficient version of weighted ratio approximation. The
cutoffs are compact on the cylinder, but both errors are in normalized torus
L². No mass is dropped where the finite tag is zero. -/
theorem torus_coefficient_smooth_disjoint_approx (o : ℝ)
    {F H : UnitAddCircle × UnitAddCircle → ℂ} (hFm : Measurable F) (hHm : Measurable H)
    (hF : MemLp F 2 slowVolume) (hH : MemLp H 2 slowVolume)
    (hzero : ∀ᵐ x ∂slowVolume, F x=0 → H x=0)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ s : SimpleFunc (ℝ × UnitAddCircle) ℂ,
    ∃ χ : ↥s.range → ℝ × UnitAddCircle → ℝ,
      (∀ i, CylinderSmooth (χ i) ∧ HasCompactSupport (χ i) ∧
        tsupport (χ i) ⊆ Ioo o (o+1) ×ˢ univ ∧ ∀ x, 0 ≤ χ i x ∧ χ i x ≤ 1) ∧
      Pairwise (fun i j => Disjoint (tsupport (χ i)) (tsupport (χ j))) ∧
      eLpNorm (fun x => F x - ∑ i, (cylinderTorusCutoff (χ i) x:ℂ)*F x) 2 slowVolume < ε ∧
      eLpNorm (fun x => H x - ∑ i, i.val*((cylinderTorusCutoff (χ i) x:ℂ)*F x)) 2 slowVolume < ε := by
  let π := cylinderToSlow
  have hπ := measurePreserving_cylinderToSlow o
  have hFm' := hFm.comp hπ.measurable
  have hHm' := hHm.comp hπ.measurable
  have hF' := hF.comp_measurePreserving hπ
  have hH' := hH.comp_measurePreserving hπ
  obtain ⟨s,χ,hχ,hd,hu,ht⟩ := coefficient_smooth_disjoint_approx (cylinderVolume o)
    hFm' hHm' hF' hH' (hπ.quasiMeasurePreserving.ae hzero)
    (isOpen_Ioo.prod isOpen_univ)
    ((cylinder_mem_open_ae o).mono (fun x hx hn => False.elim (hn hx))) hε
  simp only [comp_apply] at hu ht
  have hχsupp i : support (χ i) ⊆ Ioo o (o+1) ×ˢ univ := subset_tsupport (χ i) |>.trans (hχ i).2.2.1
  have hcm i : Measurable (χ i) := (hχ i).1.continuous.measurable
  have hum : AEStronglyMeasurable (fun x => F (cylinderToSlow x)-∑ i, (χ i x:ℂ)*F (cylinderToSlow x))
      (cylinderVolume o) :=
    (hFm'.sub (Finset.measurable_sum _ (fun i _ => (Complex.measurable_ofReal.comp (hcm i)).mul hFm'))).aestronglyMeasurable
  have htm : AEStronglyMeasurable (fun x => H (cylinderToSlow x)-∑ i, i.val*((χ i x:ℂ)*F (cylinderToSlow x)))
      (cylinderVolume o) :=
    (hHm'.sub (Finset.measurable_sum _ (fun i _ => measurable_const.mul
      ((Complex.measurable_ofReal.comp (hcm i)).mul hFm')))).aestronglyMeasurable
  have he i x : χ i (slowToCylinder o x) = cylinderTorusCutoff (χ i) x :=
    (cylinderTorusCutoff_rep (hχsupp i) x).symm
  refine ⟨s,χ,hχ,hd,?_,?_⟩
  · rw [← eLpNorm_slow_pull o _ hum] at hu
    simpa only [Function.comp_def,cylinderToSlow_slowToCylinder,he] using hu
  · rw [← eLpNorm_slow_pull o _ htm] at ht
    simpa only [Function.comp_def,cylinderToSlow_slowToCylinder,he] using ht

end ThreeTorus
end
end

section

noncomputable section
open Set Function MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal
namespace ThreeTorus

lemma vector_reindex_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : PassagePackets ι) (e : κ ≃ ι) :
    finitePacketVector (F.reindex e).m (F.reindex e).A = finitePacketVector F.m F.A := by
  funext x
  exact e.sum_comp (fun i => packet (F.m i) (F.A i) x)

lemma tagged_vector_reindex_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : PassagePackets ι) (e : κ ≃ ι) (b : ι → ℂ) :
    (fun x => ∑ i, b (e i)*packet ((F.reindex e).m i) ((F.reindex e).A i) x) =
      fun x => ∑ i, b i*packet (F.m i) (F.A i) x := by
  funext x
  exact e.sum_comp (fun i => b i*packet (F.m i) (F.A i) x)

/-- Source05 constant-ratio preparation, including all zero-tag pieces.
The finite constant tags and compact smooth supports are chosen on positive
modes, then reflected literally. No weighted null set is divided by. -/
theorem exists_reflected_ratio_packets {ι : Type} [Fintype ι]
    (F : PassagePackets ι) (hi : Injective F.m)
    {τ : ι → ι} (hr : F.Reflection τ)
    (H : ι → UnitAddCircle × UnitAddCircle → ℂ)
    (hHm : ∀ i, Measurable (H i)) (hHl : ∀ i, MemLp (H i) 2 slowVolume)
    (hHr : ∀ i p, H (τ i) p=conj (H i p))
    (hzero : ∀ i, ∀ᵐ p ∂slowVolume, F.A i p=0 → H i p=0)
    {δ ε : ℝ} (hg : F.GoodArc δ) (hε : 0 < ε) :
    ∃ n : ℕ, ∃ G : PassagePackets (Fin n), ∃ σ : Fin n → Fin n, ∃ b : Fin n → ℂ,
      G.V=F.V ∧ G.GoodArc δ ∧ Involutive σ ∧ G.Reflection σ ∧
      (∀ i, b (σ i)=conj (b i)) ∧
      (∀ i j, i ≠ j → G.m i=G.m j → Disjoint (G.cylinderCore i) (G.cylinderCore j)) ∧
      physicalDist (finitePacketVector F.m F.A) (finitePacketVector G.m G.A) < ε ∧
      physicalDist (finitePacketVector F.m H) (fun x => ∑ i, b i*packet (G.m i) (G.A i) x) < ε := by
  classical
  have hFl i : MemLp (F.A i) 2 slowVolume := (F.continuous_amplitude i).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  let η := (ε/2)/(Fintype.card (PositiveIndex F.m)+1)
  have hη : 0 < η := by dsimp [η]; positivity
  have ht (i : PositiveIndex F.m) := torus_coefficient_smooth_disjoint_approx F.o
    (F.continuous_amplitude i.val).measurable (hHm i.val) (hFl i.val) (hHl i.val)
    (hzero i.val) ((ENNReal.ofReal_pos.mpr hη).ne')
  choose s χ hχ hd hFe hHe using ht
  let J : PositiveIndex F.m → Type := fun i => ↥(s i).range
  let (i : PositiveIndex F.m) : Fintype (J i) := inferInstanceAs (Fintype ↥(s i).range)
  have hcs : ∀ k, CylinderSmooth (ratioCut F J χ k) := by
    intro k; cases k with
    | inl p => exact (hχ p.1 p.2).1
    | inr p => exact (hχ p.1 p.2).1
  have hcc : ∀ k, HasCompactSupport (ratioCut F J χ k) := by
    intro k; cases k with
    | inl p => exact (hχ p.1 p.2).2.1
    | inr p => exact (hχ p.1 p.2).2.1
  have hss : ∀ k, support (ratioCut F J χ k) ⊆ Ioo F.o (F.o+1) ×ˢ univ := by
    intro k; cases k with
    | inl p => exact (subset_tsupport _).trans (hχ p.1 p.2).2.2.1
    | inr p => exact (subset_tsupport _).trans (hχ p.1 p.2).2.2.1
  let G₀ := F.clipped (ratioRoot F J τ) (ratioCut F J χ) hcs hcc hss
  let b₀ : RatioIndex F J → ℂ := ratioTag F J (fun _ j => j.val)
  let e : Fin (Fintype.card (RatioIndex F J)) ≃ RatioIndex F J := (Fintype.equivFin _).symm
  let G := G₀.reindex e
  let σ : Fin (Fintype.card (RatioIndex F J)) → Fin (Fintype.card (RatioIndex F J)) :=
    fun i => e.symm (e i).swap
  have heσ i : e (σ i)=(e i).swap := e.apply_symm_apply _
  have hσ : Involutive σ := by intro i; simp only [σ,Equiv.apply_symm_apply,Sum.swap_swap,Equiv.symm_apply_apply]
  have hr₀ : G₀.Reflection Sum.swap := clipped_reflection hr hcs hcc hss
  have hd₀ := clipped_equal_mode_disjoint hi hr hcs hcc hss hd
  have hv : finitePacketVector G.m G.A = finitePacketVector G₀.m G₀.A := vector_reindex_equiv G₀ e
  have htv : (fun x => ∑ i, b₀ (e i)*packet (G.m i) (G.A i) x) =
      (fun x => ∑ i, b₀ i*packet (G₀.m i) (G₀.A i) x) := tagged_vector_reindex_equiv G₀ e b₀
  refine ⟨_,G,σ,b₀ ∘ e,rfl,hg,hσ,G₀.reindex_reflection hr₀ heσ,?_,?_,?_,?_⟩
  · intro i
    exact (congrArg b₀ (heσ i)).trans (ratioTag_reflect F J _ (e i))
  · intro i j hij hm
    exact hd₀ (e i) (e j) (fun h => hij (e.injective h)) hm
  · rw [hv,untagged_clipped_vector hr hcs hcc hss,
        reflectedVector_eq F.nonzero (hr.involutive hi) hr.index hr.amplitude]
    apply physicalDist_reflectedVector τ (fun i => hFl i.val) _ hε hFe
    intro i
    apply Continuous.memLp_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact continuous_finsetSum _ (fun j _ =>
      (Complex.continuous_ofReal.comp (cylinderTorusCutoff_continuous (hχ i j).1 (hχ i j).2.1)).mul
        (F.continuous_amplitude i.val))
  · change physicalDist _ (fun x => ∑ i, b₀ (e i)*packet (G.m i) (G.A i) x) < ε
    rw [htv,tagged_clipped_vector hr hcs hcc hss,
      reflectedVector_eq F.nonzero (hr.involutive hi) hr.index hHr]
    apply physicalDist_reflectedVector τ (fun i => hHl i.val) _ hε hHe
    intro i
    apply Continuous.memLp_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact continuous_finsetSum _ (fun j _ => continuous_const.mul
      ((Complex.continuous_ofReal.comp (cylinderTorusCutoff_continuous (hχ i j).1 (hχ i j).2.1)).mul
        (F.continuous_amplitude i.val)))

end ThreeTorus
end
end

section

noncomputable section
open Set Function MeasureTheory
open scoped BigOperators ComplexConjugate
namespace ThreeTorus

lemma physicalDist_add_smul {f g : TripleTorus → ℂ}
    (hf : MemLp f 2 tripleVolume) (hg : MemLp g 2 tripleVolume) (c : ℂ) :
    physicalDist f (fun x => f x+c*g x) = ‖c‖*‖hg.toLp g‖ := by
  change physicalDist f (f+c • g) = _
  rw [physicalDist_eq_norm hf (hf.add (hg.const_smul c)),MemLp.toLp_add,
    MemLp.toLp_const_smul]
  · simp only [sub_add_cancel_left,norm_neg,norm_smul]
  · exact hg
  · exact hf
  · exact hg.const_smul c

namespace PassagePackets
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
lemma append_weighted_vector (F : PassagePackets ι) (H : PassagePackets κ) {δ : ℝ}
    (hδ : 0 ≤ δ) (hgF : F.GoodArc δ) (hgH : H.GoodArc δ) (hV : H.V=F.V)
    (a b : ℂ) :
    (fun x => ∑ i, Sum.elim (fun _ => a) (fun _ => b) i *
      packet ((F.append H hδ hgF hgH hV).m i) ((F.append H hδ hgF hgH hV).A i) x) =
      fun x => a*finitePacketVector F.m F.A x+b*finitePacketVector H.m H.A x := by
  funext x
  simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,append,finitePacketVector,Finset.mul_sum]

lemma modeSum_add_amplitude (F : PassagePackets ι) (a b : ι → ℂ) (t : ℂ)
    (k : F.ModeIndex) (p : UnitAddCircle × UnitAddCircle) :
    (F.modeSum (fun i => a i+t*b i)).A k p =
      (F.modeSum a).A k p+t*(F.modeSum b).A k p := by
  classical
  change (∑ i, (if F.m i=k.val then a i+t*b i else 0)*F.A i p) =
    (∑ i, (if F.m i=k.val then a i else 0)*F.A i p)+t*∑ i, (if F.m i=k.val then b i else 0)*F.A i p
  rw [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> ring
end PassagePackets

/-- Two actual real smooth packet vectors in a common good-arc twist admit
simultaneous constant-tag clipping. Repeated modes are honestly regrouped;
zero pieces of either vector are retained before the real null-set perturbation. -/
theorem exists_ratio_packets_for_pair {ι κ : Type} [Fintype ι] [Fintype κ]
    (F : PassagePackets ι) (H : PassagePackets κ) {δ : ℝ}
    (hδ : 0 ≤ δ) (hgF : F.GoodArc δ) (hgH : H.GoodArc δ) (hV : H.V=F.V)
    (τ : ι → ι) (σ : κ → κ) (hτ : Involutive τ) (hσ : Involutive σ)
    (hrF : F.Reflection τ) (hrH : H.Reflection σ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∃ G : PassagePackets (Fin n), ∃ ρ : Fin n → Fin n, ∃ b : Fin n → ℂ,
      G.V=F.V ∧ G.GoodArc δ ∧ Involutive ρ ∧ G.Reflection ρ ∧
      (∀ i, b (ρ i)=conj (b i)) ∧
      (∀ i j, i ≠ j → G.m i=G.m j → Disjoint (G.cylinderCore i) (G.cylinderCore j)) ∧
      physicalDist (finitePacketVector F.m F.A) (finitePacketVector G.m G.A) < ε ∧
      physicalDist (finitePacketVector H.m H.A) (fun x => ∑ i, b i*packet (G.m i) (G.A i) x) < ε := by
  classical
  let U := F.append H hδ hgF hgH hV
  let a : ι ⊕ κ → ℂ := Sum.elim (fun _ => 1) (fun _ => 0)
  let b : ι ⊕ κ → ℂ := Sum.elim (fun _ => 0) (fun _ => 1)
  let B := U.modeSum a
  let C := U.modeSum b
  let r : ι ⊕ κ → ι ⊕ κ := Sum.map τ σ
  have hr : U.Reflection r := F.append_reflection H hδ hgF hgH hV hrF hrH
  have hri : Involutive r := by
    intro i; cases i with
    | inl i => exact congrArg Sum.inl (hτ i)
    | inr i => exact congrArg Sum.inr (hσ i)
  have ha : ∀ i, a (r i)=conj (a i) := by intro i; cases i <;> simp [a,r]
  have hb : ∀ i, b (r i)=conj (b i) := by intro i; cases i <;> simp [b,r]
  have hcv : finitePacketVector C.m C.A = finitePacketVector H.m H.A := by
    rw [U.modeSum_vector b,F.append_weighted_vector H hδ hgF hgH hV]
    simp only [zero_mul,one_mul,zero_add]
  have hbl i : MemLp (B.A i) 2 slowVolume := (B.continuous_amplitude i).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hcl i : MemLp (C.A i) 2 slowVolume := (C.continuous_amplitude i).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hFl : MemLp (finitePacketVector F.m F.A) 2 tripleVolume := memLp_finitePacketVector
    (fun i => (F.continuous_amplitude i).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  have hHl : MemLp (finitePacketVector H.m H.A) 2 tripleVolume := memLp_finitePacketVector
    (fun i => (H.continuous_amplitude i).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  let M := ‖hHl.toLp (finitePacketVector H.m H.A)‖+1
  have hM : 0 < M := by dsimp [M]; positivity
  obtain ⟨t,ht,htε,htz⟩ := exists_small_real_perturbation slowVolume
    (fun i => (B.continuous_amplitude i).measurable) (fun i => (C.continuous_amplitude i).measurable)
    (div_pos (half_pos hε) hM)
  let D := U.modeSum (fun i => a i+(t:ℂ)*b i)
  have hD : D.Reflection (U.modeNeg hr) := U.modeSum_reflection hri hr (by
    intro i; simp only [ha,hb,map_add,map_mul,Complex.conj_ofReal])
  have hC : C.Reflection (U.modeNeg hr) := U.modeSum_reflection hri hr hb
  have hz i : ∀ᵐ p ∂slowVolume, D.A i p=0 → C.A i p=0 := by
    simpa only [D,U.modeSum_add_amplitude] using htz i
  obtain ⟨n,G,ρ,q,hGV,hGg,hρ,hrG,hq,hd,hDG,hCG⟩ := exists_reflected_ratio_packets D
    (U.modeSum_injective _) hD C.A (fun i => (C.continuous_amplitude i).measurable)
    hcl hC.amplitude hz (U.modeSum_good _ (F.append_good H hδ hgF hgH hV)) (half_pos hε)
  have hDv : finitePacketVector D.m D.A = fun x => finitePacketVector F.m F.A x+(t:ℂ)*finitePacketVector H.m H.A x := by
    rw [U.modeSum_vector]
    have he : (fun i => a i+(t:ℂ)*b i) = Sum.elim (fun _ => 1) (fun _ => (t:ℂ)) := by
      funext i; cases i <;> simp [a,b]
    simp_rw [congrFun he]
    rw [F.append_weighted_vector H hδ hgF hgH hV]
    simp only [one_mul]
  have hDt : physicalDist (finitePacketVector F.m F.A) (finitePacketVector D.m D.A) < ε/2 := by
    rw [hDv,physicalDist_add_smul hFl hHl,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht]
    have hh := (lt_div_iff₀ hM).mp htε
    have hn := norm_nonneg (hHl.toLp (finitePacketVector H.m H.A))
    dsimp only [M] at hh
    nlinarith
  refine ⟨n,G,ρ,q,hGV,hGg,hρ,hrG,hq,hd,?_,?_⟩
  · have hDl : MemLp (finitePacketVector D.m D.A) 2 tripleVolume := memLp_finitePacketVector (fun i => (D.continuous_amplitude i).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    have hGl : MemLp (finitePacketVector G.m G.A) 2 tripleVolume := memLp_finitePacketVector (fun i => (G.continuous_amplitude i).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    exact (physicalDist_triangle hFl hDl hGl).trans_lt (by linarith)
  · change physicalDist (finitePacketVector C.m C.A) _ < ε/2 at hCG
    rw [hcv] at hCG
    exact hCG.trans (by linarith)

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal
namespace ThreeTorus

/-- A finite literal real smooth packet list. Repeated frequencies are permitted;
no orthogonality is part of this bookkeeping structure. -/
structure RealPacketFamily where
  Index : Type
  finite : Fintype Index
  data : PassagePackets Index
  neg : Index → Index
  invol : Involutive neg
  reflected : data.Reflection neg
attribute [instance] RealPacketFamily.finite
namespace RealPacketFamily
variable (F : RealPacketFamily)
def vector : TripleTorus → ℂ := finitePacketVector F.data.m F.data.A
def density : UnitAddCircle → ℝ := fun z => ∑ i, F.data.marginalDensity i z
lemma continuous_vector : Continuous F.vector :=
  continuous_finsetSum _ (fun i _ => continuous_packet (F.data.continuous_amplitude i))
lemma vector_memLp : MemLp F.vector 2 tripleVolume :=
  F.continuous_vector.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
lemma vector_real (x : TripleTorus) : conj (F.vector x)=F.vector x :=
  finitePacketVector_real F.neg F.invol F.reflected.index F.reflected.amplitude x
lemma vector_centered : (∫ x, F.vector x ∂tripleVolume)=0 :=
  finitePacket_integral_zero F.data.nonzero (fun i => (F.data.continuous_amplitude i).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _))
lemma density_nonneg (z : UnitAddCircle) : 0 ≤ F.density z :=
  Finset.sum_nonneg (fun i _ => F.data.marginalDensity_nonneg i z)
lemma density_measurable : Measurable F.density :=
  Finset.measurable_sum _ (fun i _ => F.data.marginalDensity_measurable i)
lemma density_integrable : Integrable F.density phaseHaar :=
  integrable_finsetSum _ (fun i _ => F.data.marginalDensity_integrable i)

def append (G : RealPacketFamily) {δ : ℝ} (hδ : 0 ≤ δ)
    (hF : F.data.GoodArc δ) (hG : G.data.GoodArc δ) (hV : G.data.V=F.data.V) : RealPacketFamily where
  Index := F.Index ⊕ G.Index
  finite := inferInstance
  data := F.data.append G.data hδ hF hG hV
  neg := Sum.map F.neg G.neg
  invol := by intro i; cases i with
    | inl i => exact congrArg Sum.inl (F.invol i)
    | inr i => exact congrArg Sum.inr (G.invol i)
  reflected := F.data.append_reflection G.data hδ hF hG hV F.reflected G.reflected

lemma append_vector (G : RealPacketFamily) {δ : ℝ} (hδ : 0 ≤ δ)
    (hF : F.data.GoodArc δ) (hG : G.data.GoodArc δ) (hV : G.data.V=F.data.V) :
    (F.append G hδ hF hG hV).vector = fun x => F.vector x+G.vector x := by
  funext x
  change (∑ i : F.Index ⊕ G.Index, packet (Sum.elim F.data.m G.data.m i) (Sum.elim F.data.A G.data.A i) x) = _
  rw [Fintype.sum_sum_type]
  rfl

lemma density_energy (hm : Injective F.data.m) :
    (∫ z, F.density z ∂phaseHaar)=physicalDist F.vector 0^2 := by
  let : MeasurableSpace F.Index := ⊤
  let : MeasurableSingletonClass F.Index := ⟨fun _ => trivial⟩
  have hφ : Measurable (fun u => (F.data.periodic.lift u:UnitAddCircle)) :=
    AddCircle.measurable_mk'.comp F.data.speed_continuous.measurable
  have hs := F.data.marginalDensity_sum_spectrum
  rw [← finitePacketSpectralMeasure_eq_sum hφ _ (fun i => (F.data.continuous_amplitude i).measurable)] at hs
  have he := finitePacket_energy_density hφ hm (fun i => (F.data.continuous_amplitude i).measurable)
    (fun i => (F.data.continuous_amplitude i).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    F.density_measurable F.density_nonneg hs
  rw [physicalDist_sq,physicalError]
  simpa only [vector,Pi.zero_apply,sub_zero] using he.symm
end RealPacketFamily
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

theorem exists_neutral_families (F H : RealPacketFamily) (hmi : Injective F.data.m)
    {δ : ℝ} (hδ : 0 ≤ δ) (hgF : F.data.GoodArc δ) (hgH : H.data.GoodArc δ) (hV : H.data.V=F.data.V)
    (Q : PhysicalJetData) (frame : PhysicalFrame)
    {ε η ζ : ℝ} (hε : 0 < ε) (hη : 0 < η) (hζ : 0 < ζ) :
    ∃ s : NeutralStep (F.data.append H.data hδ hgF hgH hV),
      ∃ F' H' : RealPacketFamily,
      F'.data.V=s.final.V ∧ H'.data.V=s.final.V ∧ F'.data.GoodArc s.δ ∧ H'.data.GoodArc s.δ ∧
      s.δ < η ∧ Q.Close ζ frame F.data.V (s.nextFrame frame) F'.data.V ∧ Injective F'.data.m ∧
      physicalDist F.vector (F'.vector ∘ s.chart) < ε ∧
      physicalDist H.vector (H'.vector ∘ s.chart) < ε ∧
      (∫ z, |F'.density z-F.density z| ∂phaseHaar) < ε := by
  obtain ⟨s,hsδ,hjet,hmi',⟨τ',hτ',hrF'⟩,⟨σ',hσ',hrH'⟩,hF',hH',hp⟩ :=
    exists_neutral_pair F.data H.data hmi hδ hgF hgH hV F.neg H.neg F.invol H.invol
      F.reflected H.reflected Q frame hε hη hζ
  let F' : RealPacketFamily := ⟨_,inferInstance,(s.reindex Sum.inl).final,τ',hτ',hrF'⟩
  let H' : RealPacketFamily := ⟨_,inferInstance,(s.reindex Sum.inr).final,σ',hσ',hrH'⟩
  exact ⟨s,F',H',rfl,rfl,(s.reindex Sum.inl).good,(s.reindex Sum.inr).good,hsδ,hjet,hmi',hF',hH',hp⟩

lemma physicalDist_continuous_comp (α : Equiv.Perm TripleTorus) (hc : Continuous α)
    (hm : MeasurePreserving α tripleVolume tripleVolume) (f g : TripleTorus → ℂ) :
    physicalDist (f ∘ α) (g ∘ α)=physicalDist f g := by
  unfold physicalDist physicalError
  exact congrArg Real.sqrt (hm.integral_comp (hc.measurableEmbedding α.injective) (fun x => ‖f x-g x‖^2))

lemma physicalDist_add_right (f g h : TripleTorus → ℂ) :
    physicalDist (fun x => f x+h x) (fun x => g x+h x)=physicalDist f g := by
  unfold physicalDist physicalError
  simp only [add_sub_add_right_eq_sub]

lemma densityDist_triangle {p q r : UnitAddCircle → ℝ}
    (hp : Integrable p phaseHaar) (hq : Integrable q phaseHaar) (hr : Integrable r phaseHaar) :
    (∫ z, |p z-r z| ∂phaseHaar) ≤ (∫ z, |p z-q z| ∂phaseHaar)+(∫ z, |q z-r z| ∂phaseHaar) := by
  calc
    _ ≤ ∫ z, |p z-q z|+|q z-r z| ∂phaseHaar :=
      integral_mono (hp.sub hr).abs (((hp.sub hq).abs).add ((hq.sub hr).abs))
        (fun z => abs_sub_le (p z) (q z) (r z))
    _ = _ := integral_add (hp.sub hq).abs (hq.sub hr).abs
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {d : Type*} [Fintype d]

lemma multiTrigPolynomial_add (c b : (d → ℤ) →₀ ℂ) :
    multiTrigPolynomial (c+b) = multiTrigPolynomial c+multiTrigPolynomial b := by
  unfold multiTrigPolynomial
  exact Finsupp.sum_add_index' (by intro k; exact zero_smul ℂ (UnitAddTorus.mFourier k)) (fun k a b => add_smul a b (UnitAddTorus.mFourier k))

lemma multiTrigPolynomial_smul (a : ℂ) (c : (d → ℤ) →₀ ℂ) :
    multiTrigPolynomial (a • c) = a • multiTrigPolynomial c := by
  unfold multiTrigPolynomial
  rw [Finsupp.sum_smul_index (h := fun k (a : ℂ) => a • UnitAddTorus.mFourier k) (fun k => zero_smul ℂ (UnitAddTorus.mFourier k))]
  simp only [smul_smul,Finsupp.sum,Finset.smul_sum]

lemma multiTrigPolynomial_single (k : d → ℤ) (a : ℂ) :
    multiTrigPolynomial (Finsupp.single k a) = a • UnitAddTorus.mFourier k := by
  unfold multiTrigPolynomial
  exact Finsupp.sum_single_index (h := fun k (a : ℂ) => a • UnitAddTorus.mFourier k) (zero_smul ℂ (UnitAddTorus.mFourier k))

def conjugateCoefficients (c : (d → ℤ) →₀ ℂ) : (d → ℤ) →₀ ℂ :=
  Finsupp.mapDomain (fun k => -k) (Finsupp.mapRange conj (map_zero _) c)

omit [Fintype d] in
lemma conjugateCoefficients_apply (c : (d → ℤ) →₀ ℂ) (k : d → ℤ) :
    conjugateCoefficients c k = conj (c (-k)) := by
  have h := Finsupp.mapDomain_apply_of_injective (neg_injective : Injective (fun k : d → ℤ => -k))
    (Finsupp.mapRange conj (map_zero _) c) (-k)
  simpa only [conjugateCoefficients,neg_neg,Finsupp.mapRange_apply] using h

lemma multiTrigPolynomial_conjugate (c : (d → ℤ) →₀ ℂ) (x : UnitAddTorus d) :
    multiTrigPolynomial (conjugateCoefficients c) x = conj (multiTrigPolynomial c x) := by
  simp only [multiTrigPolynomial,conjugateCoefficients]
  rw [Finsupp.sum_mapDomain_index (h := fun k (a : ℂ) => a • UnitAddTorus.mFourier k) (fun k => zero_smul ℂ (UnitAddTorus.mFourier k)) (fun k a b => add_smul a b (UnitAddTorus.mFourier k))]
  rw [Finsupp.sum_mapRange_index (h := fun k (a : ℂ) => a • UnitAddTorus.mFourier (-k)) (fun k => zero_smul ℂ (UnitAddTorus.mFourier (-k)))]
  simp only [Finsupp.sum,ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul,
    UnitAddTorus.mFourier_neg,map_sum,map_mul]

lemma integral_mFourier (k : d → ℤ) :
    (∫ x : UnitAddTorus d, UnitAddTorus.mFourier k x) = if k=0 then 1 else 0 := by
  have h := orthonormal_iff_ite.mp (UnitAddTorus.orthonormal_mFourier (d := d)) (0:d → ℤ) k
  simpa only [ContinuousMap.inner_toLp,UnitAddTorus.mFourier_zero,ContinuousMap.one_apply,
    map_one,one_mul,mul_one,eq_comm] using h

lemma integral_multiTrigPolynomial (c : (d → ℤ) →₀ ℂ) :
    (∫ x : UnitAddTorus d, multiTrigPolynomial c x) = c 0 := by
  classical
  simp only [multiTrigPolynomial_apply]
  rw [integral_finsetSum _ (fun k _ =>
    ((UnitAddTorus.mFourier k).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).const_mul (c k))]
  simp only [integral_const_mul,integral_mFourier,mul_ite,mul_one,mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · exact (Finsupp.notMem_support_iff.mp h).symm

/-- A finite FULL-torus polynomial can be made exactly real and centered,
with reflected coefficients, without changing the density statement. -/
theorem exists_real_centered_uniform_multiTrig {h : UnitAddTorus d → ℂ}
    (hh : Continuous h) (hr : ∀ x, conj (h x) = h x)
    (hc : ∫ x, h x = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : (d → ℤ) →₀ ℂ, c 0 = 0 ∧ (∀ k, c (-k)=conj (c k)) ∧
      ∀ x, ‖h x-multiTrigPolynomial c x‖ < ε := by
  classical
  obtain ⟨b,hb⟩ := exists_uniform_multiTrig hh (show 0 < ε/4 by positivity)
  let r : (d → ℤ) →₀ ℂ := (1/2:ℂ) • (b+conjugateCoefficients b)
  have hrk (k : d → ℤ) : r (-k) = conj (r k) := by
    simp only [r,Finsupp.smul_apply,Finsupp.add_apply,conjugateCoefficients_apply,
      neg_neg,smul_eq_mul,map_mul,map_div₀,map_one,map_ofNat,map_add,starRingEnd_self_apply]
    congr 1
    exact add_comm _ _
  have hrp (x : UnitAddTorus d) : multiTrigPolynomial r x =
      (multiTrigPolynomial b x+conj (multiTrigPolynomial b x))/2 := by
    simp only [r,multiTrigPolynomial_smul,multiTrigPolynomial_add,ContinuousMap.smul_apply,
      ContinuousMap.add_apply,smul_eq_mul,multiTrigPolynomial_conjugate]
    ring
  have hdist (x : UnitAddTorus d) : ‖h x-multiTrigPolynomial r x‖ < ε/4 := by
    rw [hrp]
    have he : h x-(multiTrigPolynomial b x+conj (multiTrigPolynomial b x))/2 =
        ((h x-multiTrigPolynomial b x)+conj (h x-multiTrigPolynomial b x))/2 := by
      rw [map_sub,hr x]; ring
    rw [he,norm_div]
    have hn := norm_add_le (h x-multiTrigPolynomial b x) (conj (h x-multiTrigPolynomial b x))
    simp only [Complex.norm_conj] at hn
    rw [Complex.norm_ofNat]
    linarith [hb x]
  have hint : Integrable h volume := hh.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hrint : Integrable (multiTrigPolynomial r) volume :=
    (multiTrigPolynomial r).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hr0 : ‖r 0‖ ≤ ε/4 := by
    have he : (∫ x, h x-multiTrigPolynomial r x) = -r 0 := by
      rw [integral_sub hint hrint,hc,integral_multiTrigPolynomial,zero_sub]
    have hbnd := norm_integral_le_of_norm_le (μ := (volume : Measure (UnitAddTorus d))) (integrable_const (ε/4)) (.of_forall fun x => (hdist x).le)
    simpa only [he,norm_neg,integral_const,probReal_univ,one_smul] using hbnd
  let c : (d → ℤ) →₀ ℂ := r-Finsupp.single 0 (r 0)
  have hcapply (k : d → ℤ) : c k = r k - if k=0 then r 0 else 0 := by
    simp only [c,Finsupp.sub_apply,Finsupp.single_apply,eq_comm]
  refine ⟨c,by simp [hcapply],?_,?_⟩
  · intro k
    by_cases hk : k=0
    · simp [hcapply,hk]
    · simp [hcapply,hk,hrk]
  · intro x
    have hep : multiTrigPolynomial c x = multiTrigPolynomial r x-r 0 := by
      have hec : c = r+(-1:ℂ) • Finsupp.single 0 (r 0) := by
        simp only [c,neg_one_smul,sub_eq_add_neg]
      rw [hec,multiTrigPolynomial_add,multiTrigPolynomial_smul (-1) (Finsupp.single 0 (r 0)),multiTrigPolynomial_single]
      simp only [ContinuousMap.add_apply,ContinuousMap.smul_apply,smul_eq_mul,
        UnitAddTorus.mFourier_zero,ContinuousMap.one_apply,mul_one,neg_one_mul,sub_eq_add_neg]
    rw [hep,sub_sub_eq_add_sub]
    have he : h x+r 0-multiTrigPolynomial r x = (h x-multiTrigPolynomial r x)+r 0 := by ring
    rw [he]
    exact (norm_add_le _ _).trans_lt (by linarith [hdist x])

end ThreeTorus
end
end

section
noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology
namespace ThreeTorus
/-- The coordinate convention used by the analytic packet calculations. -/
def toTriple : Torus ≃ᵐ TripleTorus :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => UnitAddCircle) 0).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl UnitAddCircle)
      (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle)))

lemma toTriple_apply (x : Torus) : toTriple x = (x 0,x 1,x 2) := rfl

lemma toTriple_symm_apply (x : TripleTorus) : toTriple.symm x = ![x.1,x.2.1,x.2.2] := by
  apply toTriple.injective
  simp only [MeasurableEquiv.apply_symm_apply,toTriple_apply,Matrix.cons_val_zero,Matrix.cons_val_one]
  rfl

lemma measurePreserving_toTriple : MeasurePreserving toTriple μ tripleVolume := by
  exact ((MeasurePreserving.id AddCircle.haarAddCircle).prod
    (measurePreserving_piFinTwo (fun _ : Fin 2 => AddCircle.haarAddCircle))).comp
      (measurePreserving_piFinSuccAbove (fun _ : Fin 3 => AddCircle.haarAddCircle) 0)

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators RealInnerProductSpace ENNReal
namespace ThreeTorus

/-- Removing a fiber mean is an orthogonal projection, with constant ONE.
This is the estimate preserving the source good-arc sqrt(beta) loss. -/
lemma integral_sq_sub_mean {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] {f : X → ℂ} (hf : MemLp f 2 μ) :
    (∫ x, ‖f x-∫ y, f y ∂μ‖^2 ∂μ) =
      (∫ x, ‖f x‖^2 ∂μ)-‖∫ y, f y ∂μ‖^2 := by
  have hi := hf.integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
  have hinner : (∫ x, inner ℝ (f x) (∫ y, f y ∂μ) ∂μ) = ‖∫ y, f y ∂μ‖^2 := by
    calc
      _ = ∫ x, inner ℝ (∫ y, f y ∂μ) (f x) ∂μ := integral_congr_ae
        (.of_forall fun x => real_inner_comm _ _)
      _ = inner ℝ (∫ y, f y ∂μ) (∫ y, f y ∂μ) := integral_inner hi _
      _ = _ := real_inner_self_eq_norm_sq _
  simp_rw [norm_sub_sq_real]
  have hn : Integrable (fun x => ‖f x‖^2) μ := hf.integrable_norm_pow (by norm_num)
  have hh : Integrable (fun x => 2*inner ℝ (f x) (∫ y, f y ∂μ)) μ :=
    (hi.inner_const (𝕜 := ℝ) (∫ y, f y ∂μ)).const_mul 2
  have ha := integral_add (hn.sub hh) (integrable_const (μ := μ) (‖∫ y, f y ∂μ‖^2))
  dsimp only [Pi.sub_apply] at ha
  rw [ha,integral_sub hn hh,integral_const,probReal_univ,one_smul,integral_const_mul,hinner]
  ring

lemma integral_sq_sub_mean_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] {f : X → ℂ} (hf : MemLp f 2 μ) :
    (∫ x, ‖f x-∫ y, f y ∂μ‖^2 ∂μ) ≤ ∫ x, ‖f x‖^2 ∂μ := by
  rw [integral_sq_sub_mean hf]
  exact sub_le_self _ (sq_nonneg _)

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate ENNReal
namespace ThreeTorus

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

abbrev TensorIndex := Fin 3 → ℤ

def tensorCharacter (k : TensorIndex) (x : TripleTorus) : ℂ :=
  fourier (k 0) x.1 * fourier (k 1) x.2.1 * fourier (k 2) x.2.2

lemma mFourier_toTriple (k : TensorIndex) (x : TripleTorus) :
    UnitAddTorus.mFourier k (toTriple.symm x) = tensorCharacter k x := by
  change (∏ i, fourier (k i) (toTriple.symm x i)) = _
  simp only [Fin.prod_univ_three,toTriple_symm_apply,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,tensorCharacter]
  rfl

def tensorPolynomial (c : TensorIndex →₀ ℂ) (x : TripleTorus) : ℂ :=
  c.sum (fun k a => a*tensorCharacter k x)

lemma tensorPolynomial_eq (c : TensorIndex →₀ ℂ) : tensorPolynomial c = multiTrigPolynomial c ∘ toTriple.symm := by
  funext x
  simp only [tensorPolynomial,multiTrigPolynomial_apply,Function.comp_apply,Finsupp.sum,mFourier_toTriple]

lemma continuous_toTriple : Continuous toTriple := by
  change Continuous (fun x : Torus => (x 0,x 1,x 2))
  fun_prop

lemma continuous_toTriple_symm : Continuous toTriple.symm := by
  simp only [show (toTriple.symm : TripleTorus → Torus) = fun x => ![x.1,x.2.1,x.2.2] from funext toTriple_symm_apply]
  exact continuous_pi (fun i => by fin_cases i <;> fun_prop)

lemma tensorCharacter_continuous (k : TensorIndex) : Continuous (tensorCharacter k) := by
  unfold tensorCharacter
  fun_prop

lemma tensorPolynomial_continuous (c : TensorIndex →₀ ℂ) : Continuous (tensorPolynomial c) := by
  rw [tensorPolynomial_eq]
  exact (multiTrigPolynomial c).continuous.comp continuous_toTriple_symm

lemma exists_real_centered_tensor {h : TripleTorus → ℂ} (hh : Continuous h)
    (hr : ∀ x, conj (h x) = h x) (hc : ∫ x, h x ∂tripleVolume = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ c : TensorIndex →₀ ℂ, c 0=0 ∧ (∀ k, c (-k)=conj (c k)) ∧
      ∀ x, ‖h x-tensorPolynomial c x‖ < ε := by
  have hm : (volume : Measure (UnitAddTorus (Fin 3))) = μ := rfl
  have hcen : ∫ x : UnitAddTorus (Fin 3), h (toTriple x) = 0 := by
    rw [hm,measurePreserving_toTriple.integral_comp toTriple.measurableEmbedding,hc]
  obtain ⟨c,hc0,hcr,hcε⟩ := exists_real_centered_uniform_multiTrig
    (hh.comp continuous_toTriple) (fun x => hr (toTriple x)) hcen hε
  refine ⟨c,hc0,hcr,fun x => ?_⟩
  simpa only [tensorPolynomial_eq,comp_apply,toTriple.apply_symm_apply] using hcε (toTriple.symm x)

/-- Angular split, first slow split, and the final centered slow average. -/
def tensorAngular (c : TensorIndex →₀ ℂ) : TensorIndex →₀ ℂ :=
  c.filter (fun k => k 0 ≠ 0)
def tensorMiddle (c : TensorIndex →₀ ℂ) : TensorIndex →₀ ℂ :=
  c.filter (fun k => k 0 = 0 ∧ k 1 ≠ 0)
def tensorLast (c : TensorIndex →₀ ℂ) : TensorIndex →₀ ℂ :=
  c.filter (fun k => k 0 = 0 ∧ k 1 = 0)

lemma tensor_split (c : TensorIndex →₀ ℂ) :
    tensorAngular c + tensorMiddle c + tensorLast c = c := by
  classical
  ext k
  simp only [tensorAngular,tensorMiddle,tensorLast,Finsupp.add_apply,Finsupp.filter_apply]
  by_cases h0 : k 0=0 <;> by_cases h1 : k 1=0 <;> simp [h0,h1]

lemma tensorLast_nonzero {c : TensorIndex →₀ ℂ} (hc : c 0=0) {k : TensorIndex}
    (hk : k ∈ (tensorLast c).support) : k 2 ≠ 0 := by
  classical
  have hh := Finsupp.mem_support_iff.1 hk
  simp only [tensorLast,Finsupp.filter_apply] at hh
  split_ifs at hh with h
  · intro hk2
    have he : k=0 := by ext i; fin_cases i <;> simp [h.1,h.2,hk2]
    exact hh (by simpa [he] using hc)
  · exact False.elim (hh rfl)

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

/-- Build literal smooth passage input coefficients from compact smooth
cylinder cutoffs and smooth periodic two-torus coefficients. -/
def cutoffPackets {ι : Type*} (m : ι → ℤ) (hm : ∀ i, m i ≠ 0)
    (C : ι → UnitAddCircle × UnitAddCircle → ℂ)
    (hCc : ∀ i, Continuous (C i))
    (hCs : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => C i (p.1,p.2)))
    (χ : ι → ℝ × UnitAddCircle → ℝ) (hχs : ∀ i, CylinderSmooth (χ i))
    (hχc : ∀ i, HasCompactSupport (χ i))
    (o l u R : ℝ) (hχo : ∀ i, support (χ i) ⊆ Ioo o (o+1) ×ˢ univ)
    (hχI : ∀ i, support (χ i) ⊆ Ioc l u ×ˢ univ)
    (hlo : o ≤ l) (huo : u ≤ o+1) (hlu : l ≤ u) (hR : 0 < R)
    (V : ℝ → ℝ) (hVp : Periodic V 1)
    (hVs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hVd : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x) : PassagePackets ι where
  m := m
  nonzero := hm
  A := fun i p => (cylinderTorusCutoff (χ i) p:ℂ)*C i p
  A₀ := fun i a x => (χ i (x,a):ℂ)*C i ((x:UnitAddCircle),a)
  o := o
  l := l
  u := u
  R := R
  lo := hlo
  uo := huo
  lu := hlu
  Rpos := hR
  lift_matches := fun i a x hx => by rw [cylinderTorusCutoff_eq (hχo i) hx]
  two := by
    intro i a
    have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        ((fun p : ℝ × UnitAddCircle => (χ i p:ℂ)*C i (p.1,p.2)) ∘ cylinderProjection) :=
      (Complex.ofRealCLM.contDiff.comp (hχs i)).mul (hCs i)
    exact ((cylinder_smooth_regular hs).1 a).of_le (WithTop.coe_le_coe.mpr (le_top : (2:ℕ∞) ≤ ⊤))
  continuous_lift := by
    intro i
    exact ((Complex.continuous_ofReal.comp (hχs i).continuous).mul
      ((hCc i).comp (QuotientAddGroup.continuous_mk.prodMap continuous_id))).comp continuous_swap
  continuous_deriv := by
    intro i
    have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        ((fun p : ℝ × UnitAddCircle => (χ i p:ℂ)*C i (p.1,p.2)) ∘ cylinderProjection) :=
      (Complex.ofRealCLM.contDiff.comp (hχs i)).mul (hCs i)
    exact (cylinder_smooth_regular hs).2.2.comp continuous_swap
  smooth_lift := fun i => (Complex.ofRealCLM.contDiff.comp (hχs i)).mul (hCs i)
  support_lift := by
    intro i a x hx
    exact (hχI i (show χ i (x,a) ≠ 0 from fun hz => hx (by simp [hz]))).1
  continuous_amplitude := fun i => (Complex.continuous_ofReal.comp
    (cylinderTorusCutoff_continuous (hχs i) (hχc i))).mul (hCc i)
  smooth_amplitude := fun i => (Complex.ofRealCLM.contDiff.comp
    (cylinderTorusCutoff_smooth (hχs i) (hχc i))).mul (hCs i)
  V := V
  periodic := hVp
  smooth_speed := hVs
  positive_deriv := hVd

end ThreeTorus
end
end

section

/-! The two different neutral separations in source05: the first separates
cylinder supports, the second separates final angular indices. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

namespace NeutralStep
variable {ι : Type*} {F : PassagePackets ι} (s : NeutralStep F)

lemma core_eq (i : PassageOutputIndex s.S) : s.final.core i =
    tsupport (passageOutputCore s.S s.cut.ψ s.χ F.m (s.geometry.H s.n) F.A s.n i) := by
  unfold PassagePackets.core
  rw [s.lift]
  congr 1
  funext x
  simp only [retainedRealAmplitude,passageOutputCore,fourier_eval_zero,mul_one]

lemma cores_disjoint
    (hd : Pairwise (fun i j => Disjoint (tsupport (s.χ i).uncurry) (tsupport (s.χ j).uncurry)))
    (i j : PassageOutputIndex s.S) (hne : i ≠ j) (he : s.final.m i = s.final.m j) :
    Disjoint (s.final.core i) (s.final.core j) := by
  rw [s.core_eq,s.core_eq]
  rw [s.mode,s.mode] at he
  exact passageOutputCore_disjoint hd i j hne he

/-- Reflection-compatible scalar cutoffs on the actual first output. Their
supports are disjoint on the frequency line, not merely on the cylinder. -/
theorem second_cutoffs [Fintype ι]
    (hd : Pairwise (fun i j => Disjoint (tsupport (s.χ i).uncurry) (tsupport (s.χ j).uncurry)))
    {τ : PassageOutputIndex s.S → PassageOutputIndex s.S}
    (hτ : Involutive τ) (hr : s.final.Reflection τ) :
    ∃ c : ℕ, 0 < c ∧ (∀ x : ℝ, (c:ℝ)+s.final.V x ≠ 0) ∧
      ∃ ξ : PassageOutputIndex s.S → ℝ → ℝ,
        (∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ξ i) ∧ HasCompactSupport (ξ i) ∧
          ξ i 0 = 0 ∧ (∀ x, 0 ≤ ξ i x ∧ ξ i x ≤ 1) ∧
          ∀ (C : Set ℝ) a x, stationaryWeight C
            (fun t => (s.final.m i:ℝ)*((c:ℝ)+s.final.V t)) (s.final.A₀ i a) x ≠ 0 → ξ i x = 1) ∧
        Pairwise (fun i j => Disjoint (tsupport (ξ i)) (tsupport (ξ j))) ∧
        ∀ i x, ξ (τ i) x = ξ i (-x) := by
  classical
  have hφi : InjOn (fun x : ℝ => s.final.periodic.lift (x:UnitAddCircle))
      (Ioo s.δ (1-s.δ)) := by
    change InjOn s.final.V (Ioo s.δ (1-s.δ))
    apply StrictMonoOn.injOn
    apply strictMonoOn_of_deriv_pos (convex_Ioo _ _) s.final.smooth_speed.continuous.continuousOn
    intro x hx
    exact s.good.2.2.2 x (interior_subset hx)
  obtain ⟨c,hc,h0,ξ,_T,hξ,hξd,_hT0,_hTd,_hTexact⟩ := second_separation_of_actual_output
    s.S s.cut.ψ s.χ F.m (s.geometry.H s.n) F.A s.n s.nonzero s.cut.ψ_compact
      (Ioo s.δ (1-s.δ)) s.cut.ψ_support hd s.final.periodic.lift s.final.speed_continuous hφi
  let η : PassageOutputIndex s.S → ℝ → ℝ := fun i x => ξ i x*ξ (τ i) (-x)
  have hsub i : tsupport (η i) ⊆ tsupport (ξ i) := tsupport_mul_subset_left
  have hξone i {x : ℝ} (hx : x ∈ (fun t => (s.final.m i:ℝ)*((c:ℝ)+s.final.V t)) ''
      s.final.core i) : ξ i x = 1 := by
    have hh := (hξ i).2.2.2.2 x
    rw [s.core_eq,s.mode] at hx
    exact (hh hx).self_of_nhds
  refine ⟨c,hc,h0,η,fun i => ⟨(hξ i).1.mul ((hξ (τ i)).1.comp contDiff_neg),
    (hξ i).2.1.mul_right,?_,?_,?_⟩,?_,?_⟩
  · simp only [η,(hξ i).2.2.1,zero_mul]
  · intro x
    exact ⟨mul_nonneg ((hξ i).2.2.2.1 x).1 ((hξ (τ i)).2.2.2.1 (-x)).1,
      (mul_le_mul ((hξ i).2.2.2.1 x).2 ((hξ (τ i)).2.2.2.1 (-x)).2
        ((hξ (τ i)).2.2.2.1 (-x)).1 zero_le_one).trans (by norm_num)⟩
  · intro C a x hx
    have hm := stationaryWeight_support_subset (s.final.support_subset_core s.spare i a) hx
    have hrm : -x ∈ (fun t => (s.final.m (τ i):ℝ)*((c:ℝ)+s.final.V t)) '' s.final.core (τ i) := by
      rcases hm with ⟨t,ht,he⟩
      refine ⟨t,(hr.core i).symm ▸ ht,?_⟩
      simp only [hr.index,Int.cast_neg,neg_mul,he]
    simp only [η,hξone i hm,hξone (τ i) hrm,mul_one]
  · intro i j hij
    exact (hξd hij).mono (hsub i) (hsub j)
  · intro i x
    simp only [η,hτ i,neg_neg,mul_comm]

end NeutralStep

end ThreeTorus
end
end

section

/-! The two neutral passages of source05, on the same literal packet family.
The first separates cylinder supports and the second makes angular modes
injective. Physical and density estimates retain each original root label. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

lemma scalar_cylinder_compact {f : ℝ → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (fun p : ℝ × UnitAddCircle => f p.1) := by
  apply (hf.prod isCompact_univ).of_isClosed_subset (isClosed_tsupport _) 
  apply closure_minimal _ (hf.isClosed.prod isClosed_univ)
  intro p hp
  exact ⟨subset_tsupport f hp,mem_univ _⟩

/-- Neither intermediate modes nor intermediate coefficients are replaced by
an independent spectral model. All estimates concern the two actual charts. -/
theorem exists_two_neutral_separations {ι : Type} [Fintype ι]
    (F : PassagePackets ι)
    (hd : ∀ i j, i ≠ j → F.m i = F.m j → Disjoint (F.cylinderCore i) (F.cylinderCore j))
    (τ : ι → ι) (hτ : Involutive τ) (hr : F.Reflection τ)
    (Q : PhysicalJetData) (frame : PhysicalFrame)
    {ε κ ζ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) (hζ : 0 < ζ) :
    ∃ s : NeutralStep F, ∃ t : NeutralStep s.final,
      Injective t.final.m ∧ t.δ < κ ∧
      (∃ τT : PassageOutputIndex t.S → PassageOutputIndex t.S,
        Involutive τT ∧ t.final.Reflection τT ∧ ∀ i, (τT i).1.1 = τ i.1.1) ∧
      Q.Close ζ frame F.V (t.nextFrame (s.nextFrame frame)) t.final.V ∧
      ∀ i, physicalError (packet (F.m i) (F.A i))
        (pairOutputVector t.final i ∘ s.chart.trans t.chart) < ε ∧
        (∫ z, |pairOutputDensity t.final i z-F.marginalDensity i z| ∂phaseHaar) < ε := by
  classical
  obtain ⟨c,hc,h0,χ,hχ,hχd,hχr⟩ := first_separation_cutoffs F hd τ hτ hr
  obtain ⟨s,hsχ,_hsc,_hsδ,hjet1,hs⟩ := exists_controlled_neutral F hc h0 χ
    (fun i => (hχ i).1) (fun i => (hχ i).2.1) (fun i => (hχ i).2.2.1)
    (fun i => (hχ i).2.2.2.1) (fun i => (hχ i).2.2.2.2) Q frame
    (show 0 < ε/8 by positivity) hκ (show 0 < ζ/2 by positivity)
  have hsd : Pairwise (fun i j => Disjoint (tsupport (s.χ i).uncurry) (tsupport (s.χ j).uncurry)) := by
    simpa only [hsχ] using hχd
  obtain ⟨τS,hτSroot,hτS,hrS⟩ := s.reflection hr hτ (by simpa only [hsχ] using hχr)
  obtain ⟨d,hdpos,hd0,ξ,hξ,hξd,hξr⟩ := s.second_cutoffs hsd hτS hrS
  obtain ⟨e,he,hecard⟩ := transmission_sum_budget s.S (show 0 < ε/8 by positivity)
  obtain ⟨t,htχ,_htc,htδ,hjet2,ht⟩ := exists_controlled_neutral s.final hdpos hd0
    (fun i x _ => ξ i x)
    (fun i => (hξ i).1.comp contDiff_fst)
    (fun i => scalar_cylinder_compact (hξ i).2.1)
    (fun i _ => (hξ i).2.2.1) (fun i x _ => (hξ i).2.2.2.1 x)
    (fun i => (hξ i).2.2.2.2) Q (s.nextFrame frame) he hκ (show 0 < ζ/2 by positivity)
  have hTd : Pairwise (fun i j => Disjoint (t.S i) (t.S j)) := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro k hki hkj
    obtain ⟨a,ha⟩ := (t.indices i k).mp hki
    obtain ⟨b,hb⟩ := (t.indices j k).mp hkj
    rw [htχ] at ha hb
    exact Set.disjoint_left.mp (hξd hij) (subset_tsupport _ ha) (subset_tsupport _ hb)
  have hTi : Injective t.final.m := by
    intro i j hij
    apply output_index_injective hTd
    simpa only [t.mode] using hij
  obtain ⟨τT,hτTroot,hτT,hrT⟩ := t.reflection hrS hτS (by
    intro i x a
    simpa only [htχ] using hξr i x)
  refine ⟨s,t,hTi,htδ,⟨τT,hτT,hrT,fun i => ?_⟩,?_,fun i => ?_⟩
  · rw [hτTroot,hτSroot]
  · exact (hjet1.trans hjet2).mono (by linarith)
  · have hphys : physicalError (outputVector s.final i)
        (pairOutputVector t.final i ∘ t.chart) < ε/8 :=
      transmission_pair_physical s.final t.final (t.geometry.Hcontinuous t.n) i
        (fun j => (ht j).1) (hecard i).2
    have hden : (∫ z, |pairOutputDensity t.final i z-outputDensity s.final i z| ∂phaseHaar) < ε/8 := by
      apply transmission_pair_density t.final s.final.density s.final.density_continuous i
        (fun j => ?_) (hecard i).1
      simpa only [s.final.marginalDensity_eq s.spare] using (ht j).2
    constructor
    · have hb := physicalError_triangle (continuous_packet (m := F.m i) (F.continuous_amplitude i))
        ((continuous_outputVector s.final i).comp (continuous_passageChart (s.geometry.Hcontinuous s.n)))
        ((continuous_pairOutputVector t.final i).comp
          ((continuous_passageChart (t.geometry.Hcontinuous t.n)).comp
            (continuous_passageChart (s.geometry.Hcontinuous s.n))))
      change physicalError (packet (F.m i) (F.A i)) (pairOutputVector t.final i ∘ s.chart.trans t.chart) ≤
        2*physicalError (packet (F.m i) (F.A i)) (outputVector s.final i ∘ s.chart) +
        2*physicalError ((outputVector s.final i) ∘ s.chart)
          ((pairOutputVector t.final i ∘ t.chart) ∘ s.chart) at hb
      have hchart := physicalError_chart (s.geometry.Hcontinuous s.n).measurable
        (outputVector s.final i) (pairOutputVector t.final i ∘ t.chart)
      change physicalError (outputVector s.final i ∘ s.chart)
        ((pairOutputVector t.final i ∘ t.chart) ∘ s.chart) = _ at hchart
      rw [hchart] at hb
      have hsphys : physicalError (packet (F.m i) (F.A i)) (outputVector s.final i ∘ s.chart) < ε/8 := (hs i).1
      linarith
    · have hb := integral_abs_sub_triangle
        (continuous_circle_integrable (continuous_pairOutputDensity t.final i))
        (continuous_circle_integrable (continuous_outputDensity s.final i))
        (F.marginalDensity_integrable i)
      linarith [(hs i).2]

end ThreeTorus
end
end

end OAI
