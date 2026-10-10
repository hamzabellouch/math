import OAI.Analysis.FiniteFactor.CrossedProduct.AngleLaw
import Mathlib.Data.Finset.Powerset

namespace OAI

namespace FiniteFactor
open MeasureTheory Finset
open scoped ENNReal Classical
noncomputable section

/-- The finite union event specifying at least q coordinate misses. -/
def coordinateMissEvent (I : Finset SourceCoordinate) (q : ℕ)
    (S : SourceCoordinate → Set ℝ) : Set (SourceCoordinate → ℝ) :=
  ⋃ J ∈ I.powersetCard q, Set.pi (J : Set SourceCoordinate) S

/-- Independence and the union bound, retaining the exact natural exponent.
This lemma uses the actual source angle law. -/
theorem coordinateMissEvent_bound (I : Finset SourceCoordinate) (q : ℕ)
    (S : SourceCoordinate → Set ℝ) (hS : ∀ i, MeasurableSet (S i))
    (b : ℝ≥0∞) (hb : ∀ i ∈ I, sourceAngleMarginal i (S i) ≤ b) :
    sourceAngleLaw (coordinateMissEvent I q S) ≤ (2 : ℝ≥0∞)^I.card * b^q := by
  classical
  have hJ (J : Finset SourceCoordinate) (hJ : J ∈ I.powersetCard q) :
      sourceAngleLaw (Set.pi (J : Set SourceCoordinate) S) ≤ b^q := by
    rcases Finset.mem_powersetCard.mp hJ with ⟨hsub, hcard⟩
    rw [sourceAngleLaw_cylinder J S (fun i _ => hS i)]
    calc
      _ ≤ ∏ _i ∈ J, b := Finset.prod_le_prod (fun i hi => hb i (hsub hi))
      _ = b^q := by simp [hcard]
  have hc : (I.powersetCard q).card ≤ 2^I.card := by
    rw [← Finset.card_powerset]
    exact Finset.card_le_card (fun J hJ => Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hJ).1)
  calc
    _ ≤ ∑ J ∈ I.powersetCard q, sourceAngleLaw (Set.pi (J : Set SourceCoordinate) S) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _J ∈ I.powersetCard q, b^q := Finset.sum_le_sum hJ
    _ = ((I.powersetCard q).card : ℝ≥0∞)*b^q := by simp [nsmul_eq_mul]
    _ ≤ (2 : ℝ≥0∞)^I.card*b^q := by
      have hc' : ((I.powersetCard q).card : ℝ≥0∞) ≤ (2 : ℝ≥0∞)^I.card := by exact_mod_cast hc
      gcongr

/-- Any realization with at least q misses lies in the union event. -/
theorem mem_coordinateMissEvent_of_card (I : Finset SourceCoordinate) (q : ℕ)
    (S : SourceCoordinate → Set ℝ) (θ : SourceCoordinate → ℝ)
    (h : q ≤ (I.filter (fun i => θ i ∈ S i)).card) : θ ∈ coordinateMissEvent I q S := by
  classical
  obtain ⟨J, hJ, hcard⟩ := Finset.exists_subset_card_eq h
  apply Set.mem_iUnion.mpr
  refine ⟨J, Set.mem_iUnion.mpr ⟨Finset.mem_powersetCard.mpr ⟨?_, hcard⟩, ?_⟩⟩
  · exact hJ.trans (Finset.filter_subset _ _)
  · intro i hi
    exact (Finset.mem_filter.mp (hJ hi)).2

end
end FiniteFactor

end OAI
