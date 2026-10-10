import OAI.NumberTheory.TotientAsymptotic.TailEncoding
import OAI.NumberTheory.TotientAsymptotic.TailBoxCoordinates

namespace OAI

/-! Full-dimensional aggregation of a finite witness family with fixed cofactor. -/

noncomputable section
open scoped BigOperators
open MeasureTheory
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def witnessPrimeRegion {H R : ℕ} (W : Finset (TailDatum H))
    (S : TailDatum H → Set (Fin R → ℝ)) (p : Fin (H-P H) → ℕ) : Set (Fin R → ℝ) :=
  ⋃ η ∈ W.filter (fun η => tailPrimeVector η=p), S η

def witnessBoxRegion {H R : ℕ} (W : Finset (TailDatum H))
    (S : TailDatum H → Set (Fin R → ℝ)) (b : Fin (H-P H) → ℕ) : Set (Fin R → ℝ) :=
  ⋃ η ∈ W.filter (fun η => tailVector η ∈ unitGridCell b), S η

lemma witnessPrimeRegion_eq {H R a : ℕ} {s : ℝ} (W : Finset (TailDatum H))
    (S : TailDatum H → Set (Fin R → ℝ))
    (hW : ∀ η ∈ W, IsWitness H s η) (hcof : ∀ η ∈ W, η.cofactor=a)
    {η : TailDatum H} (hη : η ∈ W) : witnessPrimeRegion W S (tailPrimeVector η) = S η := by
  ext u
  simp only [witnessPrimeRegion, Set.mem_iUnion, Finset.mem_filter]
  constructor
  · rintro ⟨ξ, ⟨hξ, he⟩, hu⟩
    have hh : ξ=η := tailDatum_eq_of_primeVector (hW ξ hξ) (hW η hη)
      ((hcof ξ hξ).trans (hcof η hη).symm) he
    simpa only [hh] using hu
  · intro hu
    exact ⟨η, ⟨hη, rfl⟩, hu⟩

/-- Aggregation counts the prime mass of each tail box once. The bound has
no factor equal to the number of witnesses in the box. -/
theorem witness_tail_box_aggregation {H R a : ℕ} {s : ℝ}
    (W : Finset (TailDatum H)) (S : TailDatum H → Set (Fin R → ℝ))
    (K : Finset (Fin (H-P H) → ℕ)) (T : Set (Fin (R+(H-P H)) → ℝ)) (C : ℝ)
    (hC : 0 ≤ C) (hW : ∀ η ∈ W, IsWitness H s η) (hcof : ∀ η ∈ W, η.cofactor=a)
    (hS : ∀ η ∈ W, MeasurableSet (S η)) (hT : volume T ≠ ⊤)
    (hcover : ∀ η ∈ W, tailPrimeVector η ∈ gridPrimeTuples K)
    (hbox : ∀ b ∈ K, (∏ i, unitPrimeWeight (b i)) ≤ C)
    (henclose : ∀ η ∈ W, ∀ b ∈ K, tailVector η ∈ unitGridCell b →
      ∀ u ∈ S η, ∀ v ∈ unitGridCell b, joinCoordinates R (H-P H) (u,v) ∈ T) :
    (∑ η ∈ W, reciprocalShiftWeight (tailPrimeVector η)*volume.real (S η)) ≤ C*volume.real T := by
  classical
  have hinj : Set.InjOn tailPrimeVector (↑W : Set (TailDatum H)) := by
    intro η hη ξ hξ he
    exact tailDatum_eq_of_primeVector (hW η hη) (hW ξ hξ)
      ((hcof η hη).trans (hcof ξ hξ).symm) he
  have heq : (∑ η ∈ W, reciprocalShiftWeight (tailPrimeVector η)*volume.real (S η)) =
      ∑ p ∈ W.image tailPrimeVector, reciprocalShiftWeight p *
        volume.real (witnessPrimeRegion W S p) := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro η hη
    rw [witnessPrimeRegion_eq W S hW hcof hη]
  rw [heq]
  have hsub : W.image tailPrimeVector ⊆ gridPrimeTuples K := by
    intro p hp
    obtain ⟨η, hη, rfl⟩ := Finset.mem_image.mp hp
    exact hcover η hη
  apply (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ =>
    mul_nonneg (reciprocalShiftWeight_nonneg p) measureReal_nonneg)).trans
  apply tail_box_aggregation_enclosure K (witnessPrimeRegion W S) (witnessBoxRegion W S) T C hC
  · intro b _
    exact (W.filter _).measurableSet_biUnion (fun η hη => hS η (Finset.mem_filter.mp hη).1)
  · exact hT
  · intro b _ p hp u hu
    obtain ⟨η, hu⟩ := Set.mem_iUnion.mp hu
    obtain ⟨hη, hu⟩ := Set.mem_iUnion.mp hu
    obtain ⟨hη, he⟩ := Finset.mem_filter.mp hη
    have hc : tailVector η ∈ unitGridCell b := by
      rw [tailVector_eq_primeCoord, he]
      exact (mem_primeBoxTuples_iff.mp hp).2
    exact Set.mem_iUnion.mpr ⟨η, Set.mem_iUnion.mpr ⟨Finset.mem_filter.mpr ⟨hη, hc⟩, hu⟩⟩
  · exact hbox
  · intro z hz
    obtain ⟨⟨u,v⟩, hz, rfl⟩ := hz
    obtain ⟨b, hz⟩ := Set.mem_iUnion.mp hz
    obtain ⟨hb, hu, hv⟩ := Set.mem_iUnion.mp hz
    obtain ⟨η, hu⟩ := Set.mem_iUnion.mp hu
    obtain ⟨hη, hu⟩ := Set.mem_iUnion.mp hu
    obtain ⟨hη, hcell⟩ := Finset.mem_filter.mp hη
    exact henclose η hη b hb hcell u hu v hv

end TotientAsymptotic

end

end OAI
