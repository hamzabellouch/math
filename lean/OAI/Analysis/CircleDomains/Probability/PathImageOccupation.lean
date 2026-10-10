import OAI.Analysis.CircleDomains.Modulus.PathHausdorffLength
import OAI.Analysis.CircleDomains.Probability.DyadicMeasurePartition
import OAI.Analysis.CircleDomains.Probability.PathOccupation
import Mathlib.MeasureTheory.Measure.Regular

namespace OAI

/-! The Hausdorff measure of a path image counts each point once; arclength
occupation counts every traversal. Compact time sets and fine dyadic covers
prove the resulting measure domination without an injectivity assumption. -/

open Set Function Filter MeasureTheory Metric
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

lemma eventually_dyadic_cells_inside_compact {K V : Set PathTime}
    (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V) :
    ∀ᶠ n : ℕ in atTop, ∀ i : Fin (2 ^ n),
      (Icc (dyadicLeft n i) (dyadicRight n i) ∩ K).Nonempty →
      Icc (dyadicLeft n i) (dyadicRight n i) ⊆ V := by
  obtain ⟨δ, hδ, hd⟩ := hK.exists_thickening_subset_open hV hKV
  have hp : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hz : Tendsto (fun n : ℕ => 1 / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hp
  filter_upwards [(tendsto_order.mp hz).2 δ hδ] with n hn i hi t ht
  obtain ⟨s, hs, hsK⟩ := hi
  exact hd (mem_thickening_iff.mpr ⟨s, hsK, (dyadicCell_dist_le n i ht hs).trans_lt hn⟩)

lemma exists_small_dyadic_images_ge {X : Type*} [MetricSpace X]
    (γ : C(PathTime, X)) {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ ∀ i : Fin (2 ^ n),
      ediam (γ '' Icc (dyadicLeft n i) (dyadicRight n i)) ≤ ENNReal.ofReal ε := by
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous γ.continuous) ε hε
  have hp : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hz : Tendsto (fun n : ℕ => 1 / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hp
  obtain ⟨n, hn, hN⟩ := (((tendsto_order.mp hz).2 δ hδ).and (eventually_ge_atTop N)).exists
  refine ⟨n, hN, fun i => ediam_le ?_⟩
  rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal (hd ((dyadicCell_dist_le n i hs ht).trans_lt hn)).le

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

lemma path_hausdorff_image_compact_le_open (γ : RectifiablePath X)
    {K V : Set PathTime} (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V) :
    (μH[1] : Measure X) (γ.val '' K) ≤ pathLengthMeasure γ V := by
  let r : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hr : ∀ n, 0 < r n := fun n => by dsimp [r]; positivity
  choose k hkn hk using fun n => exists_small_dyadic_images_ge γ.val (hr n) n
  let A : ∀ n : ℕ, Fin (2 ^ k n) → Set X :=
    fun n i => γ.val '' (Icc (dyadicLeft (k n) i) (dyadicRight (k n) i) ∩ K)
  have hcover (n : ℕ) : γ.val '' K ⊆ ⋃ i, A n i := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨i, hi⟩ := exists_dyadicCell_mem (k n) t
    exact mem_iUnion.mpr ⟨i, t, ⟨hi, ht⟩, rfl⟩
  have hrad : Tendsto (fun n => ENNReal.ofReal (r n)) atTop (𝓝 0) := by
    simpa only [r, ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        tendsto_one_div_add_atTop_nhds_zero_nat
  have hfine : ∀ᶠ n : ℕ in atTop, ∀ i : Fin (2 ^ k n),
      (Icc (dyadicLeft (k n) i) (dyadicRight (k n) i) ∩ K).Nonempty →
      Icc (dyadicLeft (k n) i) (dyadicRight (k n) i) ⊆ V :=
    (tendsto_atTop_mono hkn tendsto_id).eventually
      (eventually_dyadic_cells_inside_compact hK hV hKV)
  apply (Measure.hausdorffMeasure_le_liminf_sum 1 (γ.val '' K)
    (fun n => ENNReal.ofReal (r n)) hrad A
    (Eventually.of_forall fun n i => (ediam_mono (image_mono inter_subset_left)).trans (hk n i))
    (Eventually.of_forall hcover)).trans
  apply liminf_le_of_frequently_le'
  apply Filter.Eventually.frequently
  filter_upwards [hfine] with n hn
  simp only [ENNReal.rpow_one]
  calc
    ∑ i, ediam (A n i) ≤ ∑ i : Fin (2 ^ k n),
        (pathLengthMeasure γ).restrict (Icc (dyadicLeft (k n) i) (dyadicRight (k n) i)) V := by
      apply Finset.sum_le_sum
      intro i _
      rw [Measure.restrict_apply hV.measurableSet]
      by_cases hi : (Icc (dyadicLeft (k n) i) (dyadicRight (k n) i) ∩ K).Nonempty
      · rw [inter_eq_self_of_subset_right (hn i hi), pathLengthMeasure_Icc γ (dyadicLeft_le_right _ _)]
        apply ediam_le
        rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
        exact eVariationOn.edist_le γ.val hs.1 ht.1
      · have he : A n i = ∅ := by simp only [A, not_nonempty_iff_eq_empty.mp hi, image_empty]
        rw [he, ediam_empty]
        exact bot_le
    _ = pathLengthMeasure γ V := by
      rw [← Measure.finsetSum_apply, sum_dyadic_restrict]

lemma path_hausdorff_image_compact_le_length (γ : RectifiablePath X)
    {K : Set PathTime} (hK : IsCompact K) :
    (μH[1] : Measure X) (γ.val '' K) ≤ pathLengthMeasure γ K := by
  rw [K.measure_eq_iInf_isOpen (pathLengthMeasure γ)]
  exact le_iInf fun V => le_iInf fun hKV => le_iInf fun hV =>
    path_hausdorff_image_compact_le_open γ hK hV hKV

/-- A curve's occupation dominates Hausdorff measure on its image, even
when the curve retraces itself. -/
theorem path_image_hausdorff_le_occupation (γ : RectifiablePath X) :
    (μH[1] : Measure X).restrict (range γ.val) ≤ pathOccupation γ := by
  let ν := (μH[1] : Measure X).restrict (range γ.val)
  have hfin : ν univ < ∞ := by
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact (path_hausdorff_length_le_variation γ.val).trans_lt (lt_top_iff_ne_top.mpr γ.property)
  let : IsFiniteMeasure ν := ⟨hfin⟩
  apply Measure.le_iff.mpr
  intro S hS
  change ν S ≤ pathOccupation γ S
  rw [hS.measure_eq_iSup_isClosed_of_ne_top (measure_ne_top ν S)]
  apply iSup_le
  intro F
  apply iSup_le
  intro hFS
  apply iSup_le
  intro hF
  apply le_trans ?_ (measure_mono hFS)
  change (μH[1] : Measure X).restrict (range γ.val) F ≤ pathOccupation γ F
  rw [Measure.restrict_apply hF.measurableSet, pathOccupation_apply γ hF.measurableSet]
  have he : F ∩ range γ.val = γ.val '' (γ.val ⁻¹' F) := by
    ext x
    simp only [mem_inter_iff, mem_range, mem_image, mem_preimage]
    aesop
  rw [he]
  exact path_hausdorff_image_compact_le_length γ (hF.preimage γ.val.continuous).isCompact

end CircleDomainRigidity

end

end OAI
