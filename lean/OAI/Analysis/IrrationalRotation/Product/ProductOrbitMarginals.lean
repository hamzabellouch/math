import OAI.Analysis.IrrationalRotation.Product.ProductTailTrimming
import OAI.Analysis.IrrationalRotation.Rotation.WeightedGraphMarginals

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

namespace Invariant233.ProductModel.TailTrimming

theorem rotationIterate_inverse_left (θ : ℕ → ℝ) (k : ℤ) (x : Base) :
    rotationIterate θ (-k) (rotationIterate θ k x) = x := by
  change ProductCocycle.rotate θ (-k) (ProductCocycle.rotate θ k x) = x
  rw [← ProductCocycle.rotate_add, add_neg_cancel, ProductCocycle.rotate_zero]

theorem orbitPairMeasure_first_marginal (θ : ℕ → ℝ) (n : ℕ)
    (w : Base → ℝ≥0∞) :
    (orbitPairMeasure θ n w).map Prod.fst = baseMeasure.withDensity w := by
  exact WeightedGraphMarginals.map_fst_graph _
    (ProductCocycle.measurePreserving_rotate θ (n : ℤ)).measurable

theorem orbitPairMeasure_second_marginal (θ : ℕ → ℝ) (n : ℕ)
    (w : Base → ℝ≥0∞) (hw : Measurable w) :
    (orbitPairMeasure θ n w).map Prod.snd =
      baseMeasure.withDensity (fun y => w (rotationIterate θ (-(n : ℤ)) y)) := by
  exact (WeightedGraphMarginals.map_snd_graph (baseMeasure.withDensity w)
    (T := rotationIterate θ (n : ℤ))
    (ProductCocycle.measurePreserving_rotate θ (n : ℤ)).measurable).trans
    (WeightedGraphMarginals.map_withDensity_inverse baseMeasure
      (ProductCocycle.measurePreserving_rotate θ (n : ℤ))
      (ProductCocycle.measurePreserving_rotate θ (-(n : ℤ))).measurable
      (rotationIterate_inverse_left θ (n : ℤ)) hw)

theorem orbitAverageMeasure_first_marginal (θ : ℕ → ℝ) (N : Finset ℕ)
    (w : ℕ → Base → ℝ≥0∞) (hw : ∀ n ∈ N, Measurable (w n)) :
    (orbitAverageMeasure θ N w).map Prod.fst =
      baseMeasure.withDensity (fun x => (N.card : ℝ≥0∞)⁻¹ * ∑ n ∈ N, w n x) := by
  rw [orbitAverageMeasure, Measure.map_smul _ measurable_fst.aemeasurable,
    WeightedGraphMarginals.map_finset_sum _ _ measurable_fst]
  simp_rw [orbitPairMeasure_first_marginal]
  rw [show (fun x => (N.card : ℝ≥0∞)⁻¹ * ∑ n ∈ N, w n x) =
    (N.card : ℝ≥0∞)⁻¹ • (fun x => ∑ n ∈ N, w n x) from rfl,
    withDensity_smul _ (Finset.measurable_sum N hw),
    WeightedGraphMarginals.withDensity_finset_sum baseMeasure N w hw]

theorem orbitAverageMeasure_second_marginal (θ : ℕ → ℝ) (N : Finset ℕ)
    (w : ℕ → Base → ℝ≥0∞) (hw : ∀ n ∈ N, Measurable (w n)) :
    (orbitAverageMeasure θ N w).map Prod.snd =
      baseMeasure.withDensity (fun y => (N.card : ℝ≥0∞)⁻¹ *
        ∑ n ∈ N, w n (rotationIterate θ (-(n : ℤ)) y)) := by
  rw [orbitAverageMeasure, Measure.map_smul _ measurable_snd.aemeasurable,
    WeightedGraphMarginals.map_finset_sum _ _ measurable_snd]
  have hwi (n : ℕ) (hn : n ∈ N) :
      Measurable (fun y => w n (rotationIterate θ (-(n : ℤ)) y)) :=
    (hw n hn).comp (ProductCocycle.measurePreserving_rotate θ (-(n : ℤ))).measurable
  rw [show (fun y => (N.card : ℝ≥0∞)⁻¹ *
      ∑ n ∈ N, w n (rotationIterate θ (-(n : ℤ)) y)) =
    (N.card : ℝ≥0∞)⁻¹ •
      (fun y => ∑ n ∈ N, w n (rotationIterate θ (-(n : ℤ)) y)) from rfl,
    withDensity_smul _ (Finset.measurable_sum N hwi),
    WeightedGraphMarginals.withDensity_finset_sum baseMeasure N _ hwi]
  congr 1
  exact Finset.sum_congr rfl fun n hn => orbitPairMeasure_second_marginal θ n (w n) (hw n hn)

theorem orbitPairMeasure_restrict (θ : ℕ → ℝ) (n : ℕ)
    (w : Base → ℝ≥0∞) (A : Set EndpointPair) (hA : MeasurableSet A) :
    (orbitPairMeasure θ n w).restrict A =
      orbitPairMeasure θ n ((orbitPairMap θ n ⁻¹' A).indicator w) := by
  unfold orbitPairMeasure
  rw [Measure.restrict_map (measurable_orbitPairMap θ n) hA,
    restrict_withDensity ((measurable_orbitPairMap θ n) hA),
    ← withDensity_indicator ((measurable_orbitPairMap θ n) hA)]

theorem orbitAverageMeasure_restrict (θ : ℕ → ℝ) (N : Finset ℕ)
    (w : ℕ → Base → ℝ≥0∞) (A : Set EndpointPair) (hA : MeasurableSet A) :
    (orbitAverageMeasure θ N w).restrict A =
      orbitAverageMeasure θ N (fun n => (orbitPairMap θ n ⁻¹' A).indicator (w n)) := by
  unfold orbitAverageMeasure
  rw [Measure.restrict_smul]
  have hsum : (∑ n ∈ N, orbitPairMeasure θ n (w n)).restrict A =
      ∑ n ∈ N, (orbitPairMeasure θ n (w n)).restrict A := by
    simp only [← Measure.restrictₗ_apply, map_sum]
  rw [hsum]
  congr 1
  exact Finset.sum_congr rfl fun n _ => orbitPairMeasure_restrict θ n (w n) A hA

theorem orbitAverageMeasure_restrict_first_marginal (θ : ℕ → ℝ) (N : Finset ℕ)
    (w : ℕ → Base → ℝ≥0∞) (hw : ∀ n ∈ N, Measurable (w n))
    (A : Set EndpointPair) (hA : MeasurableSet A) :
    ((orbitAverageMeasure θ N w).restrict A).map Prod.fst =
      baseMeasure.withDensity (fun x => (N.card : ℝ≥0∞)⁻¹ *
        ∑ n ∈ N, (orbitPairMap θ n ⁻¹' A).indicator (w n) x) := by
  rw [orbitAverageMeasure_restrict θ N w A hA]
  exact orbitAverageMeasure_first_marginal θ N _
    (fun n hn => (hw n hn).indicator ((measurable_orbitPairMap θ n) hA))

theorem orbitAverageMeasure_restrict_second_marginal (θ : ℕ → ℝ) (N : Finset ℕ)
    (w : ℕ → Base → ℝ≥0∞) (hw : ∀ n ∈ N, Measurable (w n))
    (A : Set EndpointPair) (hA : MeasurableSet A) :
    ((orbitAverageMeasure θ N w).restrict A).map Prod.snd =
      baseMeasure.withDensity (fun y => (N.card : ℝ≥0∞)⁻¹ *
        ∑ n ∈ N, (orbitPairMap θ n ⁻¹' A).indicator (w n)
          (rotationIterate θ (-(n : ℤ)) y)) := by
  rw [orbitAverageMeasure_restrict θ N w A hA]
  exact orbitAverageMeasure_second_marginal θ N _
    (fun n hn => (hw n hn).indicator ((measurable_orbitPairMap θ n) hA))

theorem ofReal_average_eq (N : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ n ∈ N, 0 ≤ w n) :
    ENNReal.ofReal ((N.card : ℝ)⁻¹ * ∑ n ∈ N, w n) =
      (N.card : ℝ≥0∞)⁻¹ * ∑ n ∈ N, ENNReal.ofReal (w n) := by
  rcases N.eq_empty_or_nonempty with rfl | hN
  · simp
  have hc : 0 < (N.card : ℝ) := by exact_mod_cast hN.card_pos
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr hc.le), ENNReal.ofReal_inv_of_pos hc,
    ENNReal.ofReal_natCast, ENNReal.ofReal_sum_of_nonneg hw]

theorem orbitAverageMeasure_first_marginal_real (θ : ℕ → ℝ) (N : Finset ℕ)
    (w : ℕ → Base → ℝ) (hw : ∀ n ∈ N, Measurable (w n))
    (hw0 : ∀ n ∈ N, ∀ x, 0 ≤ w n x) :
    (orbitAverageMeasure θ N (fun n x => ENNReal.ofReal (w n x))).map Prod.fst =
      baseMeasure.withDensity (fun x => ENNReal.ofReal
        ((N.card : ℝ)⁻¹ * ∑ n ∈ N, w n x)) := by
  rw [orbitAverageMeasure_first_marginal θ N _ (fun n hn => (hw n hn).ennreal_ofReal)]
  congr 1
  funext x
  exact (ofReal_average_eq N (fun n => w n x) (fun n hn => hw0 n hn x)).symm

theorem orbitAverageMeasure_second_marginal_real (θ : ℕ → ℝ) (N : Finset ℕ)
    (w : ℕ → Base → ℝ) (hw : ∀ n ∈ N, Measurable (w n))
    (hw0 : ∀ n ∈ N, ∀ x, 0 ≤ w n x) :
    (orbitAverageMeasure θ N (fun n x => ENNReal.ofReal (w n x))).map Prod.snd =
      baseMeasure.withDensity (fun y => ENNReal.ofReal
        ((N.card : ℝ)⁻¹ * ∑ n ∈ N, w n (rotationIterate θ (-(n : ℤ)) y))) := by
  rw [orbitAverageMeasure_second_marginal θ N _ (fun n hn => (hw n hn).ennreal_ofReal)]
  congr 1
  funext y
  exact (ofReal_average_eq N _ (fun n hn => hw0 n hn _)).symm

end Invariant233.ProductModel.TailTrimming

end

end OAI
