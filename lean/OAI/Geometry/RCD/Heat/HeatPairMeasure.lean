import OAI.Geometry.RCD.Heat.HeatDetailedBalance

namespace OAI

/-! # Symmetry of the measure on pairs induced by the heat flow -/

open Set Filter MeasureTheory Metric TopologicalSpace ProbabilityTheory
open scoped NNReal ENNReal Topology ProbabilityTheory

noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem heatRadonMeasure_set_lintegral (t : ℝ) (ht : 0 < t)
    {s u : Set X} (_hs : MeasurableSet s) (hu : MeasurableSet u)
    (hfs : hausdorff n X s ≠ ∞) :
    (∫⁻ x in s, hX.heatRadonMeasure hn p t ht x u ∂hausdorff n X) =
      ENNReal.ofReal (∫ x in s, (hX.heatRadonMeasure hn p t ht x).real u ∂hausdorff n X) := by
  let μ := hausdorff n X
  let : IsFiniteMeasure (μ.restrict s) := ⟨by simpa using hfs.lt_top⟩
  have hm : Measurable (fun x => (hX.heatRadonMeasure hn p t ht x).real u) :=
    ((hX.heatMarkovKernel hn p t ht).measurable_coe hu).ennreal_toReal
  have hb (x : X) : |(hX.heatRadonMeasure hn p t ht x).real u| ≤ 1 := by
    rw [abs_of_nonneg (show 0 ≤ (hX.heatRadonMeasure hn p t ht x).real u from ENNReal.toReal_nonneg)]
    calc
      _ ≤ (hX.heatRadonMeasure hn p t ht x).real univ :=
        measureReal_mono (subset_univ _) (measure_ne_top _ _)
      _ = 1 := hX.heatRadonMeasure_real_mass_one hn p t ht x
  have hi : Integrable (fun x => (hX.heatRadonMeasure hn p t ht x).real u) (μ.restrict s) :=
    (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable (Eventually.of_forall hb)
  rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)]
  apply lintegral_congr
  intro x
  exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm

/-- The reference measure paired with its Markov transition. -/
def heatPairMeasure (t : ℝ) (ht : 0 < t) : Measure (X × X) :=
  hausdorff n X ⊗ₘ hX.heatMarkovKernel hn p t ht

theorem heatPairMeasure_rectangle_balance (t : ℝ) (ht : 0 < t)
    {s u : Set X} (hs : MeasurableSet s) (hu : MeasurableSet u)
    (hfs : hausdorff n X s ≠ ∞) (hfu : hausdorff n X u ≠ ∞) :
    hX.heatPairMeasure hn p t ht (s ×ˢ u) = hX.heatPairMeasure hn p t ht (u ×ˢ s) := by
  simp only [heatPairMeasure, Measure.compProd_apply_prod hs hu,
    Measure.compProd_apply_prod hu hs]
  change (∫⁻ x in s, hX.heatRadonMeasure hn p t ht x u ∂hausdorff n X) =
    ∫⁻ y in u, hX.heatRadonMeasure hn p t ht y s ∂hausdorff n X
  rw [hX.heatRadonMeasure_set_lintegral hn p t ht hs hu hfs,
    hX.heatRadonMeasure_set_lintegral hn p t ht hu hs hfu,
    hX.heatRadonMeasure_set_balance hn p t ht hs hu hfs hfu]

theorem heatPairMeasure_rectangle_le (t : ℝ) (ht : 0 < t)
    {s u : Set X} (hs : MeasurableSet s) (hu : MeasurableSet u) :
    hX.heatPairMeasure hn p t ht (s ×ˢ u) ≤ hausdorff n X s := by
  rw [heatPairMeasure, Measure.compProd_apply_prod hs hu]
  calc
    _ ≤ ∫⁻ _ in s, (1 : ℝ≥0∞) ∂hausdorff n X := lintegral_mono fun x => prob_le_one
    _ = _ := by simp

theorem heatPairMeasure_restrict_symm (t : ℝ) (ht : 0 < t)
    {s : Set X} (hs : MeasurableSet s) (hfs : hausdorff n X s ≠ ∞) :
    (hX.heatPairMeasure hn p t ht).restrict (s ×ˢ s) =
      ((hX.heatPairMeasure hn p t ht).map Prod.swap).restrict (s ×ˢ s) := by
  let M := hX.heatPairMeasure hn p t ht
  let : IsFiniteMeasure (M.restrict (s ×ˢ s)) :=
    ⟨by simpa using (hX.heatPairMeasure_rectangle_le hn p t ht hs hs).trans_lt hfs.lt_top⟩
  apply Measure.ext_prod
  intro A B hA hB
  rw [Measure.restrict_apply (hA.prod hB), Measure.restrict_apply (hA.prod hB),
    prod_inter_prod, Measure.map_apply measurable_swap ((hA.inter hs).prod (hB.inter hs)),
    preimage_swap_prod]
  exact hX.heatPairMeasure_rectangle_balance hn p t ht (hA.inter hs) (hB.inter hs)
    ((measure_mono inter_subset_right).trans_lt hfs.lt_top).ne
    ((measure_mono inter_subset_right).trans_lt hfs.lt_top).ne

/-- Detailed balance holds for the entire sigma-finite pair measure,
not just for compactly supported tests. -/
theorem heatPairMeasure_symm (t : ℝ) (ht : 0 < t) :
    hX.heatPairMeasure hn p t ht = (hX.heatPairMeasure hn p t ht).map Prod.swap := by
  have hcover : (⋃ i : ℕ, closedBall p (i : ℝ) ×ˢ closedBall p (i : ℝ)) = univ := by
    apply eq_univ_of_forall
    intro z
    obtain ⟨i, hi⟩ := exists_nat_ge (max (dist z.1 p) (dist z.2 p))
    exact mem_iUnion.mpr ⟨i, ⟨(le_max_left _ _).trans hi, (le_max_right _ _).trans hi⟩⟩
  apply Measure.ext_of_iUnion_eq_univ hcover
  intro i
  exact hX.heatPairMeasure_restrict_symm hn p t ht measurableSet_closedBall
    ((isCompact_closedBall p (i : ℝ)).measure_lt_top.ne)

/-- The constructed heat kernel preserves the original Hausdorff measure. -/
theorem heatMarkovKernel_invariant (t : ℝ) (ht : 0 < t) :
    hX.heatMarkovKernel hn p t ht ∘ₘ hausdorff n X = hausdorff n X := by
  rw [← Measure.snd_compProd]
  change (hX.heatPairMeasure hn p t ht).snd = _
  rw [hX.heatPairMeasure_symm hn p t ht, Measure.snd_map_swap]
  exact Measure.fst_compProd _ _

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
