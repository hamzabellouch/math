import OAI.MeasureTheory.Falconer.Geometry.BallTruncation

namespace OAI

/-! # Simultaneously enforcing the finitely many slice ball bounds -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {X ι : Type*} [PseudoMetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] [Fintype ι]

def finiteBallGood (μ : Measure X) (r : ι → ℝ) (B : ι → ℝ≥0∞) : Set X :=
  {x | ∀ i, μ (ball x (2*r i)) ≤ B i}

theorem finiteBallGood_measurable (μ : Measure X) [SFinite μ]
    (r : ι → ℝ) (B : ι → ℝ≥0∞) : MeasurableSet (finiteBallGood μ r B) := by
  simp only [finiteBallGood,ofPred_forall]
  exact MeasurableSet.iInter (fun i => measurableSet_le (measurable_ball_mass μ (2*r i)) measurable_const)

omit [SecondCountableTopology X] [BorelSpace X] in
theorem finiteBallGood_compl_mass (μ : Measure X) [SFinite μ]
    (r : ι → ℝ) (B : ι → ℝ≥0∞) :
    μ (finiteBallGood μ r B)ᶜ ≤ ∑ i, μ {x | B i < μ (ball x (2*r i))} := by
  have he : (finiteBallGood μ r B)ᶜ = ⋃ i, {x | B i < μ (ball x (2*r i))} := by
    ext x
    simp [finiteBallGood,not_forall,not_le]
  rw [he]
  exact measure_iUnion_fintype_le _ _

theorem finiteBallGood_pair_loss (μ : Measure X) [SFinite μ]
    (r : ι → ℝ) (B : ι → ℝ≥0∞) (hB : ∀ i, B i ≠ 0) :
    μ (finiteBallGood μ r B)ᶜ ≤
      ∑ i, (B i)⁻¹*(μ.prod μ) {z | dist z.1 z.2 < 2*r i} :=
  (finiteBallGood_compl_mass μ r B).trans
    (Finset.sum_le_sum (fun i _ => excessive_ball_mass μ (2*r i) (hB i)))

omit [SecondCountableTopology X] [Fintype ι] in
theorem finiteBallGood_ball_bound (μ : Measure X) [SFinite μ]
    (r : ι → ℝ) (B : ι → ℝ≥0∞) (i : ι) (a : X) :
    (μ.restrict (finiteBallGood μ r B)) (ball a (r i)) ≤ B i := by
  calc
    _ ≤ (μ.restrict {x | μ (ball x (2*r i)) ≤ B i}) (ball a (r i)) :=
      Measure.restrict_mono_set μ (s := finiteBallGood μ r B)
        (t := {x | μ (ball x (2*r i)) ≤ B i}) (fun _ hx => hx i) _
    _ ≤ _ := restricted_good_ball_bound μ (r i) (B i) a

theorem finiteBallGood_mass_accounting (μ : Measure X) [SFinite μ]
    (r : ι → ℝ) (B : ι → ℝ≥0∞) :
    μ univ ≤ (μ.restrict (finiteBallGood μ r B)) univ +
      ∑ i, μ {x | B i < μ (ball x (2*r i))} := by
  rw [Measure.restrict_apply_univ]
  calc
    _ = μ (finiteBallGood μ r B)+μ (finiteBallGood μ r B)ᶜ :=
      (measure_add_measure_compl (finiteBallGood_measurable μ r B)).symm
    _ ≤ _ := add_le_add_right (finiteBallGood_compl_mass μ r B) _

end Falconer

end OAI
