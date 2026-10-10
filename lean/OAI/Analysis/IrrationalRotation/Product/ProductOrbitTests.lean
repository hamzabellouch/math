import OAI.Analysis.IrrationalRotation.Product.ProductOrbitMarginals
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Invariant233.ProductModel.TailTrimming

def orbitTestWeight (θ : ℕ → ℝ) (A : Set EndpointPair)
    (w : ℕ → Base → ℝ) (n : ℕ) : Base → ℝ :=
  (orbitPairMap θ n ⁻¹' A).indicator (w n)

theorem measurable_orbitTestWeight (θ : ℕ → ℝ) (A : Set EndpointPair)
    (hA : MeasurableSet A) (w : ℕ → Base → ℝ) (n : ℕ)
    (hw : Measurable (w n)) : Measurable (orbitTestWeight θ A w n) :=
  hw.indicator ((measurable_orbitPairMap θ n) hA)

theorem orbitTestWeight_nonneg (θ : ℕ → ℝ) (A : Set EndpointPair)
    (w : ℕ → Base → ℝ) (n : ℕ) (hw0 : ∀ x, 0 ≤ w n x) (x : Base) :
    0 ≤ orbitTestWeight θ A w n x :=
  Set.indicator_nonneg (fun x _ => hw0 x) x

theorem orbitTestWeight_inverse (θ : ℕ → ℝ) (A : Set EndpointPair)
    (w : ℕ → Base → ℝ) (n : ℕ) (y : Base) :
    orbitTestWeight θ A w n (rotationIterate θ (-(n : ℤ)) y) =
      A.indicator (fun xy : EndpointPair => w n xy.1)
        (rotationIterate θ (-(n : ℤ)) y, y) := by
  classical
  have hr : rotationIterate θ (n : ℤ) (rotationIterate θ (-(n : ℤ)) y) = y := by
    simpa only [neg_neg] using rotationIterate_inverse_left θ (-(n : ℤ)) y
  simp only [orbitTestWeight, Set.indicator_apply, Set.mem_preimage, orbitPairMap, hr]

theorem orbitAverageMeasure_restrict_real (θ : ℕ → ℝ) (N : Finset ℕ)
    (w : ℕ → Base → ℝ) (A : Set EndpointPair) (hA : MeasurableSet A) :
    (orbitAverageMeasure θ N (fun n x => ENNReal.ofReal (w n x))).restrict A =
      orbitAverageMeasure θ N (fun n x => ENNReal.ofReal (orbitTestWeight θ A w n x)) := by
  rw [orbitAverageMeasure_restrict θ N _ A hA]
  congr 1
  funext n x
  by_cases hx : orbitPairMap θ n x ∈ A <;>
    simp [orbitTestWeight, hx]

theorem orbitAverageMeasure_restrict_first_marginal_real (θ : ℕ → ℝ) (N : Finset ℕ)
    (w : ℕ → Base → ℝ) (hw : ∀ n ∈ N, Measurable (w n))
    (hw0 : ∀ n ∈ N, ∀ x, 0 ≤ w n x)
    (A : Set EndpointPair) (hA : MeasurableSet A) :
    ((orbitAverageMeasure θ N (fun n x => ENNReal.ofReal (w n x))).restrict A).map Prod.fst =
      baseMeasure.withDensity (fun x => ENNReal.ofReal
        ((N.card : ℝ)⁻¹ * ∑ n ∈ N, orbitTestWeight θ A w n x)) := by
  rw [orbitAverageMeasure_restrict_real θ N w A hA]
  exact orbitAverageMeasure_first_marginal_real θ N _
    (fun n hn => measurable_orbitTestWeight θ A hA w n (hw n hn))
    (fun n hn => orbitTestWeight_nonneg θ A w n (hw0 n hn))

theorem orbitAverageMeasure_restrict_second_marginal_real (θ : ℕ → ℝ) (N : Finset ℕ)
    (w : ℕ → Base → ℝ) (hw : ∀ n ∈ N, Measurable (w n))
    (hw0 : ∀ n ∈ N, ∀ x, 0 ≤ w n x)
    (A : Set EndpointPair) (hA : MeasurableSet A) :
    ((orbitAverageMeasure θ N (fun n x => ENNReal.ofReal (w n x))).restrict A).map Prod.snd =
      baseMeasure.withDensity (fun y => ENNReal.ofReal
        ((N.card : ℝ)⁻¹ * ∑ n ∈ N,
          orbitTestWeight θ A w n (rotationIterate θ (-(n : ℤ)) y))) := by
  rw [orbitAverageMeasure_restrict_real θ N w A hA]
  exact orbitAverageMeasure_second_marginal_real θ N _
    (fun n hn => measurable_orbitTestWeight θ A hA w n (hw n hn))
    (fun n hn => orbitTestWeight_nonneg θ A w n (hw0 n hn))

theorem orbitAverageMeasure_real_test_mass (θ : ℕ → ℝ) (N : Finset ℕ)
    (w : ℕ → Base → ℝ) (hw : ∀ n ∈ N, Measurable (w n))
    (hw0 : ∀ n ∈ N, ∀ x, 0 ≤ w n x)
    (A : Set EndpointPair) (hA : MeasurableSet A) :
    (orbitAverageMeasure θ N (fun n x => ENNReal.ofReal (w n x))).real A =
      ∫ x, (N.card : ℝ)⁻¹ * ∑ n ∈ N, orbitTestWeight θ A w n x ∂baseMeasure := by
  have he := congrArg (fun μ : Measure Base => μ univ)
    (orbitAverageMeasure_restrict_first_marginal_real θ N w hw hw0 A hA)
  simp only [Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ,
    Measure.restrict_apply_univ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ] at he
  rw [Measure.real, he]
  symm
  apply integral_eq_lintegral_of_nonneg_ae
  · apply Filter.Eventually.of_forall
    intro x
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg (fun n hn => orbitTestWeight_nonneg θ A w n (hw0 n hn) x))
  · exact (measurable_const.mul (Finset.measurable_sum N
      (fun n hn => measurable_orbitTestWeight θ A hA w n (hw n hn)))).aestronglyMeasurable

end Invariant233.ProductModel.TailTrimming

end

end OAI
