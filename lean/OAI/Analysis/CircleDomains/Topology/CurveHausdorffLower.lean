import OAI.Analysis.CircleDomains.Topology.CurveLowerDistance
import OAI.Analysis.CircleDomains.Topology.CurveHausdorffUpper
import Mathlib.MeasureTheory.Constructions.Polish.Basic

namespace OAI

/-! Lower distance estimates on countably many pieces give the reverse
arclength bound for an injective C1 curve. -/
open Set Function Filter MeasureTheory Metric Bornology
open scoped ENNReal NNReal Topology
noncomputable section
namespace CircleDomainRigidity

lemma lower_distance_hausdorff
    {γ : ℝ → ℂ} {U S : Set ℝ} (hSU : S ⊆ U) (k : ℝ≥0)
    (h : ∀ a ∈ U, ∀ b ∈ U, (k : ℝ) * dist a b ≤ dist (γ a) (γ b)) :
    (k : ℝ≥0∞) * volume S ≤ (μH[1] : Measure ℂ) (γ '' S) := by
  by_cases hk : k = 0
  · simp [hk]
  have hkR : (0 : ℝ) < k := by exact_mod_cast pos_iff_ne_zero.mpr hk
  let T : Set U := {x | (x : ℝ) ∈ S}
  let g : U → ℂ := fun x => γ x
  have hg : AntilipschitzWith k⁻¹ g := by
    apply AntilipschitzWith.of_le_mul_dist
    intro a b
    change dist (a : ℝ) (b : ℝ) ≤ (k⁻¹ : ℝ≥0) * dist (γ a) (γ b)
    rw [NNReal.coe_inv, inv_mul_eq_div, le_div_iff₀ hkR]
    simpa only [mul_comm] using h a a.property b b.property
  have hT : Subtype.val '' T = S := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hx
      exact ⟨⟨x, hSU hx⟩, hx, rfl⟩
  have hmeasure : (μH[1] : Measure U) T = volume S := by
    rw [← isometry_subtype_coe.hausdorffMeasure_image (Or.inl (by norm_num : (0 : ℝ) ≤ 1)), hT,
      hausdorffMeasure_real]
  have himage : g '' T = γ '' S := by
    change (γ ∘ Subtype.val) '' T = γ '' S
    rw [image_comp, hT]
  have hb := hg.le_hausdorffMeasure_image (by norm_num : (0 : ℝ) ≤ 1) T
  rw [hmeasure, himage, ENNReal.rpow_one, ENNReal.coe_inv hk] at hb
  have hk0 : (k : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hk
  calc
    (k : ℝ≥0∞) * volume S ≤ (k : ℝ≥0∞) * ((k : ℝ≥0∞)⁻¹ * (μH[1] : Measure ℂ) (γ '' S)) :=
      mul_le_mul' le_rfl hb
    _ = (μH[1] : Measure ℂ) (γ '' S) := by
      rw [← mul_assoc, ENNReal.mul_inv_cancel hk0 ENNReal.coe_ne_top, one_mul]

lemma derivative_lower_distance_partition
    {D : Set ℝ} (hD : IsOpen D) (hne : D.Nonempty)
    {γ : ℝ → ℂ} {d : ℝ → ℝ →L[ℝ] ℂ}
    (hd : ∀ x ∈ D, HasStrictFDerivAt γ (d x) x) (hc : ContinuousOn d D)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (A : ℕ → Set ℝ) (k : ℕ → ℝ≥0),
      (∀ n, MeasurableSet (A n)) ∧ Pairwise (Disjoint on A) ∧ (⋃ n, A n) = D ∧
      (∀ n a, a ∈ A n → ∀ b ∈ A n, (k n : ℝ) * dist a b ≤ dist (γ a) (γ b)) ∧
      ∀ n y, y ∈ A n → ‖d y‖ ≤ (k n : ℝ) + ε := by
  classical
  let : Nonempty D := hne.to_subtype
  choose U hUo hxU hUD hnorm hdist using fun x : D =>
    local_curve_lower_distance hD hd hc x.property (show 0 < ε / 2 by linarith)
  let k : D → ℝ≥0 := fun x => ⟨max (‖d x‖ - ε / 2) 0, le_max_right _ _⟩
  have hkdist : ∀ x : D, ∀ a ∈ U x, ∀ b ∈ U x,
      (k x : ℝ) * dist a b ≤ dist (γ a) (γ b) := by
    intro x a ha b hb
    change max (‖d (x : ℝ)‖ - ε / 2) 0 * dist a b ≤ dist (γ a) (γ b)
    by_cases hx : 0 ≤ ‖d (x : ℝ)‖ - ε / 2
    · simpa only [max_eq_left hx] using hdist x a ha b hb
    · simp only [max_eq_right (le_of_not_ge hx), zero_mul, dist_nonneg]
  have hknorm : ∀ x : D, ∀ y ∈ U x, ‖d y‖ ≤ (k x : ℝ) + ε := by
    intro x y hy
    have hm := le_max_left (‖d (x : ℝ)‖ - ε / 2) 0
    have hn := hnorm x y hy
    change ‖d y‖ ≤ max (‖d (x : ℝ)‖ - ε / 2) 0 + ε
    linarith
  have hcov : D ⊆ ⋃ x : D, U x := fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
  have hlin : IsLindelof D := (isLindelof_iff_lindelofSpace).mpr inferInstance
  obtain ⟨v, hv⟩ := hlin.indexed_countable_subcover U hUo hcov
  let A : ℕ → Set ℝ := disjointed (fun n => U (v n))
  have hAU : ∀ n, A n ⊆ U (v n) := fun n => disjointed_subset _ n
  refine ⟨A, fun n => k (v n),
    (fun n => MeasurableSet.disjointed (fun j => (hUo (v j)).measurableSet) n),
    disjoint_disjointed _, ?_, ?_, ?_⟩
  · change (⋃ n, disjointed (fun j => U (v j)) n) = D
    rw [iUnion_disjointed]
    exact (iUnion_subset (fun n => hUD (v n))).antisymm hv
  · exact fun n a ha b hb => hkdist (v n) a (hAU n ha) b (hAU n hb)
  · exact fun n y hy => hknorm (v n) y (hAU n hy)

lemma curve_hausdorff_lower_add_error
    {D : Set ℝ} (hD : IsOpen D) {γ : ℝ → ℂ} {d : ℝ → ℝ →L[ℝ] ℂ}
    (hd : ∀ x ∈ D, HasStrictFDerivAt γ (d x) x) (hc : ContinuousOn d D)
    (hi : InjOn γ D) {S : Set ℝ} (hS : MeasurableSet S) (hSD : S ⊆ D)
    {ε : ℝ} (hε : 0 < ε) :
    (∫⁻ t in S, ENNReal.ofReal ‖d t‖) ≤
      (μH[1] : Measure ℂ) (γ '' S) + ENNReal.ofReal ε * volume S := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨A, k, hA, hdisj, hcover, hdist, hnorm⟩ :=
    derivative_lower_distance_partition hD (hne.mono hSD) hd hc hε
  have hsets : (⋃ n, S ∩ A n) = S := by
    rw [← inter_iUnion, hcover, inter_eq_left.mpr hSD]
  have hdj : Pairwise (Disjoint on fun n => S ∩ A n) :=
    fun i j hij => (hdisj hij).mono inter_subset_right inter_subset_right
  have hcont : ContinuousOn γ D := fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have him : ∀ n, MeasurableSet (γ '' (S ∩ A n)) := fun n =>
    (hS.inter (hA n)).image_of_continuousOn_injOn
      (hcont.mono (inter_subset_left.trans hSD)) (hi.mono (inter_subset_left.trans hSD))
  have hidj : Pairwise (Disjoint on fun n => γ '' (S ∩ A n)) := fun i j hij =>
    (hdj hij).image hi (inter_subset_left.trans hSD) (inter_subset_left.trans hSD)
  calc
    (∫⁻ t in S, ENNReal.ofReal ‖d t‖) =
        ∑' n, ∫⁻ t in S ∩ A n, ENNReal.ofReal ‖d t‖ := by
      rw [← lintegral_iUnion (fun n => hS.inter (hA n)) hdj, hsets]
    _ ≤ ∑' n, ((μH[1] : Measure ℂ) (γ '' (S ∩ A n)) + ENNReal.ofReal ε * volume (S ∩ A n)) := by
      apply ENNReal.tsum_le_tsum
      intro n
      have hb : (∫⁻ t in S ∩ A n, ENNReal.ofReal ‖d t‖) ≤
          ((k n : ℝ≥0∞) + ENNReal.ofReal ε) * volume (S ∩ A n) := by
        rw [← Measure.restrict_apply_univ, ← lintegral_const]
        apply setLIntegral_mono' (hS.inter (hA n))
        intro t ht
        rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_add (NNReal.coe_nonneg _) hε.le]
        exact ENNReal.ofReal_le_ofReal (hnorm n t ht.2)
      rw [add_mul] at hb
      exact hb.trans (add_le_add
        (lower_distance_hausdorff inter_subset_right (k n) (hdist n)) le_rfl)
    _ = (∑' n, (μH[1] : Measure ℂ) (γ '' (S ∩ A n))) +
        ENNReal.ofReal ε * ∑' n, volume (S ∩ A n) := by
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
    _ = (μH[1] : Measure ℂ) (γ '' S) + ENNReal.ofReal ε * volume S := by
      rw [← measure_iUnion hidj him, ← measure_iUnion hdj (fun n => hS.inter (hA n)),
        ← image_iUnion, hsets]

lemma curve_hausdorff_lower
    {D : Set ℝ} (hD : IsOpen D) {γ : ℝ → ℂ} {d : ℝ → ℝ →L[ℝ] ℂ}
    (hd : ∀ x ∈ D, HasStrictFDerivAt γ (d x) x) (hc : ContinuousOn d D)
    (hi : InjOn γ D) {S : Set ℝ} (hS : MeasurableSet S) (hb : IsBounded S) (hSD : S ⊆ D) :
    (∫⁻ t in S, ENNReal.ofReal ‖d t‖) ≤ (μH[1] : Measure ℂ) (γ '' S) := by
  have hεlim : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / (n + 1 : ℝ))) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have ht := (tendsto_const_nhds (x := (μH[1] : Measure ℂ) (γ '' S))).add
    (ENNReal.Tendsto.mul_const hεlim (Or.inr (hb.measure_lt_top (μ := volume)).ne))
  simp only [zero_mul, add_zero] at ht
  exact ge_of_tendsto' ht (fun (n : ℕ) => curve_hausdorff_lower_add_error hD hd hc hi hS hSD
    (ε := 1 / (n + 1 : ℝ)) (one_div_pos.mpr (by positivity)))

lemma curve_hausdorff_eq_integral
    {D : Set ℝ} (hD : IsOpen D) {γ : ℝ → ℂ} {d : ℝ → ℝ →L[ℝ] ℂ}
    (hd : ∀ x ∈ D, HasStrictFDerivAt γ (d x) x) (hc : ContinuousOn d D)
    (hi : InjOn γ D) {S : Set ℝ} (hS : MeasurableSet S) (hb : IsBounded S) (hSD : S ⊆ D) :
    (μH[1] : Measure ℂ) (γ '' S) = ∫⁻ t in S, ENNReal.ofReal ‖d t‖ :=
  (curve_hausdorff_upper hD hd hc hS hb hSD).antisymm
    (curve_hausdorff_lower hD hd hc hi hS hb hSD)

end CircleDomainRigidity

end

end OAI
