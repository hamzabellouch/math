import OAI.Analysis.FiniteFactor.FiniteMixtureAlgebra
import Mathlib.MeasureTheory.Measure.WithDensity

namespace OAI

namespace FiniteFactor
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
variable {ι X : Type*} [DecidableEq ι] [MeasurableSpace X]

variable (μ ν : ι → Measure X) [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]

def finiteChoiceLaw (I : Finset ι) : Measure (ι → X) := by
  letI : ∀ i, IsProbabilityMeasure (if i ∈ I then ν i else μ i) :=
    fun i => by split_ifs <;> infer_instance
  exact Measure.infinitePi (fun i => if i ∈ I then ν i else μ i)

instance finiteChoiceLaw_probability (I : Finset ι) : IsProbabilityMeasure (finiteChoiceLaw μ ν I) := by
  unfold finiteChoiceLaw
  infer_instance

def finiteAverageLaw (F : Finset ι) : Measure (ι → X) := by
  letI : ∀ i, IsProbabilityMeasure (if i ∈ F then probabilityAverage (μ i) (ν i) else μ i) :=
    fun i => by split_ifs <;> infer_instance
  exact Measure.infinitePi (fun i => if i ∈ F then probabilityAverage (μ i) (ν i) else μ i)

instance finiteAverageLaw_probability (F : Finset ι) : IsProbabilityMeasure (finiteAverageLaw μ ν F) := by
  unfold finiteAverageLaw
  infer_instance

theorem finiteChoiceLaw_update_base (I : Finset ι) (i : ι) (hi : i ∉ I) :
    coordinateUpdateLaw i (μ i) (finiteChoiceLaw μ ν I) = finiteChoiceLaw μ ν I := by
  unfold coordinateUpdateLaw finiteChoiceLaw
  rw [infinitePi_update_law]
  congr 1
  funext k
  by_cases hk : k = i
  · subst k; simp [hi]
  · simp [Function.update_of_ne hk]

theorem finiteChoiceLaw_update_replace (I : Finset ι) (i : ι) :
    coordinateUpdateLaw i (ν i) (finiteChoiceLaw μ ν I) = finiteChoiceLaw μ ν (insert i I) := by
  unfold coordinateUpdateLaw finiteChoiceLaw
  rw [infinitePi_update_law]
  congr 1
  funext k
  by_cases hk : k = i
  · subst k; simp
  · simp [hk]

theorem finiteAverageLaw_insert (F : Finset ι) (i : ι) :
    finiteAverageLaw μ ν (insert i F) =
      coordinateUpdateLaw i (probabilityAverage (μ i) (ν i)) (finiteAverageLaw μ ν F) := by
  unfold coordinateUpdateLaw finiteAverageLaw
  rw [infinitePi_update_law]
  congr 1
  funext k
  by_cases hk : k = i
  · subst k; simp
  · simp [hk]

variable {μ ν}

theorem coordinateUpdateLaw_smul_right (i : ι) (μ : Measure X) (ν : Measure (ι → X))
    [SFinite μ] [SFinite ν] (c : ℝ≥0∞) :
    coordinateUpdateLaw i μ (c • ν) = c • coordinateUpdateLaw i μ ν := by
  unfold coordinateUpdateLaw
  rw [Measure.prod_smul_right,
    Measure.map_smul _ (measurable_coordinateUpdate i).aemeasurable]

theorem coordinateUpdateLaw_finset_sum {A : Type*} (i : ι) (μ : Measure X)
    (ν : A → Measure (ι → X)) [SFinite μ] [∀ a, IsFiniteMeasure (ν a)] (S : Finset A) :
    coordinateUpdateLaw i μ (∑ a ∈ S, ν a) = ∑ a ∈ S, coordinateUpdateLaw i μ (ν a) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [coordinateUpdateLaw]
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha,coordinateUpdateLaw_add_right,Finset.sum_insert ha,ih]

/-- The finite independent diagonal-or-replacement mixture is an exact finite
sum of the laws for each replacement pattern. -/
theorem finiteAverageLaw_eq_sum (μ ν : ι → Measure X)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] (F : Finset ι) :
    finiteAverageLaw μ ν F = ((2 : ℝ≥0∞)⁻¹)^F.card •
      ∑ I ∈ F.powerset, finiteChoiceLaw μ ν I := by
  induction F using Finset.induction_on with
  | empty => simp [finiteAverageLaw,finiteChoiceLaw]
  | @insert i F hi ih =>
    rw [finiteAverageLaw_insert,coordinateUpdateLaw_average,ih,
      coordinateUpdateLaw_smul_right,coordinateUpdateLaw_smul_right,
      coordinateUpdateLaw_finset_sum,coordinateUpdateLaw_finset_sum]
    have hb : (∑ I ∈ F.powerset, coordinateUpdateLaw i (μ i) (finiteChoiceLaw μ ν I)) =
        ∑ I ∈ F.powerset, finiteChoiceLaw μ ν I := by
      apply Finset.sum_congr rfl
      intro I hI
      apply finiteChoiceLaw_update_base
      exact fun h => hi ((Finset.mem_powerset.mp hI) h)
    simp_rw [finiteChoiceLaw_update_replace]
    rw [hb,← smul_add,smul_smul,Finset.sum_powerset_insert hi,
      Finset.card_insert_of_notMem hi,pow_succ]
    rw [mul_comm]

end
end FiniteFactor

end OAI
