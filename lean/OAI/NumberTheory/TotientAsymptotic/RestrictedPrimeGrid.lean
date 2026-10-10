import OAI.NumberTheory.TotientAsymptotic.FullPrimeGrid

namespace OAI

/-! Prime-box summation for a specified subfamily of the actual basic tuples. -/

noncomputable section
open scoped BigOperators
open MeasureTheory
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def restrictedPrimeGrid (x : ℝ) (H : ℕ) (Q : Finset (Fin (L x H) → ℕ)) :=
  (fullPrimeGrid x H).filter (fun b => ∃ p ∈ Q, primePrefixCoord p ∈ unitGridCell b)

lemma restrictedPrimeTuples_subset_grid {x : ℝ} {H : ℕ}
    {Q : Finset (Fin (L x H) → ℕ)} (hQ : Q ⊆ fullPrimeTuples x H) :
    Q ⊆ gridPrimeTuples (restrictedPrimeGrid x H Q) := by
  intro p hp
  obtain ⟨b,hb,hpb⟩ := Finset.mem_biUnion.mp (fullPrimeTuples_subset_grid x H (hQ hp))
  have hc := (mem_primeBoxTuples_iff.mp hpb).2
  exact Finset.mem_biUnion.mpr ⟨b,Finset.mem_filter.mpr ⟨hb,p,hp,hc⟩,hpb⟩

lemma restrictedPrimeGrid_enclosure {x : ℝ} {H : ℕ}
    {Q : Finset (Fin (L x H) → ℕ)} {T : Set (Fin (L x H) → ℝ)}
    (henclose : ∀ p ∈ Q, ∀ v, (∀ i, |primePrefixCoord p i-v i| ≤ 1) → v ∈ T) :
    gridRegion (restrictedPrimeGrid x H Q) ⊆ T := by
  intro v hv
  obtain ⟨b,hv⟩ := Set.mem_iUnion.mp hv
  obtain ⟨hb,hvb⟩ := Set.mem_iUnion.mp hv
  obtain ⟨_,p,hp,hpb⟩ := Finset.mem_filter.mp hb
  exact henclose p hp v (unitGridCell_coordinate_distance hpb hvb)

theorem restricted_prime_mass_bound (hford : FordUnitPrimeBoxInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ {x : ℝ} {H : ℕ}, 0 ≤ theta x → P H ≤ m x →
      ∀ (Q : Finset (Fin (L x H) → ℕ)) (T : Set (Fin (L x H) → ℝ)),
      Q ⊆ fullPrimeTuples x H → volume T ≠ ⊤ →
      (∀ p ∈ Q, ∀ v, (∀ i, |primePrefixCoord p i-v i| ≤ 1) → v ∈ T) →
      (∑ p ∈ Q, reciprocalShiftWeight p) ≤
        (1+bandPrimeError C (9/10) (P H))*volume.real T := by
  obtain ⟨C,hC,hgrid⟩ := banded_grid_prime_mass_error hford
  refine ⟨C,hC,?_⟩
  intro x H hs hPm Q T hQ hT he
  have hg := hgrid hs (by norm_num : (0 : ℝ) < 9/10) hPm
    (restrictedPrimeGrid x H Q) (by
      intro b hb i
      exact bandGrid_bounds (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).1 i)
  change |gridPrimeMass (N := L x H) (restrictedPrimeGrid x H Q)-
    (volume (gridRegion (N := L x H) (restrictedPrimeGrid x H Q))).toReal| ≤
      (volume (gridRegion (N := L x H) (restrictedPrimeGrid x H Q))).toReal*
        bandPrimeError C (9/10) (P H) at hg
  have hfac : 0 ≤ 1+bandPrimeError C (9/10) (P H) := by
    linarith [bandPrimeError_nonneg hC.le (by norm_num : (0 : ℝ) < 9/10) (P H)]
  have hv : volume.real (gridRegion (restrictedPrimeGrid x H Q)) ≤ volume.real T :=
    ENNReal.toReal_mono hT (measure_mono (restrictedPrimeGrid_enclosure he))
  calc
    _ ≤ gridPrimeMass (restrictedPrimeGrid x H Q) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (restrictedPrimeTuples_subset_grid hQ)
        (fun p _ _ => reciprocalShiftWeight_nonneg p)
    _ ≤ (1+bandPrimeError C (9/10) (P H))*
        volume.real (gridRegion (restrictedPrimeGrid x H Q)) := by
      have hh := (le_abs_self _).trans hg
      change gridPrimeMass _ ≤ _*(volume (gridRegion (restrictedPrimeGrid x H Q))).toReal
      change gridPrimeMass _-(volume (gridRegion _)).toReal ≤ _ at hh
      exact (sub_le_iff_le_add.mp hh).trans_eq (by ring)
    _ ≤ _ := mul_le_mul_of_nonneg_left hv hfac

end TotientAsymptotic

end

end OAI
