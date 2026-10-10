import OAI.NumberTheory.TotientAsymptotic.PrimeBoxGeometry
import Mathlib.MeasureTheory.Constructions.Pi

namespace OAI

/-! Aggregate all discrete tails in a box before measuring the continuous
prefix. No factor counting the number of tail witnesses occurs. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace TotientAsymptotic

def tailBoxLift {R T : ℕ} (K : Finset (Fin T → ℕ))
    (U : (Fin T → ℕ) → Set (Fin R → ℝ)) :
    Set ((Fin R → ℝ) × (Fin T → ℝ)) :=
  ⋃ b ∈ K, U b ×ˢ unitGridCell b

lemma measurableSet_tailBoxLift {R T : ℕ} (K : Finset (Fin T → ℕ))
    (U : (Fin T → ℕ) → Set (Fin R → ℝ))
    (hU : ∀ b ∈ K, MeasurableSet (U b)) : MeasurableSet (tailBoxLift K U) :=
  K.measurableSet_biUnion (fun b hb => (hU b hb).prod (measurableSet_unitGridCell b))

lemma volume_tailBoxLift {R T : ℕ} (K : Finset (Fin T → ℕ))
    (U : (Fin T → ℕ) → Set (Fin R → ℝ))
    (hU : ∀ b ∈ K, MeasurableSet (U b)) :
    volume (tailBoxLift K U) = ∑ b ∈ K, volume (U b) := by
  unfold tailBoxLift
  rw [measure_biUnion_finset]
  · apply Finset.sum_congr rfl
    intro b _
    rw [Measure.volume_eq_prod, Measure.prod_prod, volume_unitGridCell, mul_one]
  · intro b _ c _ hbc
    exact Set.disjoint_left.mpr (fun z hz hw =>
      Set.disjoint_left.mp (unitGridCell_disjoint hbc) hz.2 hw.2)
  · intro b hb
    exact (hU b hb).prod (measurableSet_unitGridCell b)

lemma volumeReal_tailBoxLift {R T : ℕ} (K : Finset (Fin T → ℕ))
    (U : (Fin T → ℕ) → Set (Fin R → ℝ))
    (hU : ∀ b ∈ K, MeasurableSet (U b)) (hfin : ∀ b ∈ K, volume (U b) ≠ ⊤) :
    volume.real (tailBoxLift K U) = ∑ b ∈ K, volume.real (U b) := by
  simp only [measureReal_def, volume_tailBoxLift K U hU, ENNReal.toReal_sum hfin]

/-- A common prefix envelope for every tail in one unit box costs only the
reciprocal prime mass of that box. Summing disjoint tail boxes then gives
one full-dimensional volume. -/
theorem tail_box_aggregation {R T : ℕ} (K : Finset (Fin T → ℕ))
    (S : (Fin T → ℕ) → Set (Fin R → ℝ))
    (U : (Fin T → ℕ) → Set (Fin R → ℝ)) (C : ℝ)
    (hU : ∀ b ∈ K, MeasurableSet (U b)) (hfin : ∀ b ∈ K, volume (U b) ≠ ⊤)
    (hsub : ∀ b ∈ K, ∀ p ∈ primeBoxTuples b, S p ⊆ U b)
    (hmass : ∀ b ∈ K, (∏ i, unitPrimeWeight (b i)) ≤ C) :
    (∑ p ∈ gridPrimeTuples K, reciprocalShiftWeight p * volume.real (S p)) ≤
      C * volume.real (tailBoxLift K U) := by
  classical
  rw [gridPrimeTuples, Finset.sum_biUnion
    (fun b _ c _ hbc => primeBoxTuples_disjoint hbc),
    volumeReal_tailBoxLift K U hU hfin, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  calc
    _ ≤ ∑ p ∈ primeBoxTuples b, reciprocalShiftWeight p * volume.real (U b) := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left (measureReal_mono (hsub b hb p hp) (hfin b hb))
        (reciprocalShiftWeight_nonneg p)
    _ = (∏ i, unitPrimeWeight (b i))*volume.real (U b) := by
      rw [← Finset.sum_mul, prime_box_mass]
    _ ≤ C*volume.real (U b) := mul_le_mul_of_nonneg_right (hmass b hb) measureReal_nonneg

end TotientAsymptotic

end

end OAI
