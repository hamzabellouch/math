import OAI.NumberTheory.TotientAsymptotic.PrimeGrid

namespace OAI

/-! The geometric volumes of the same disjoint boxes used in the prime sum. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace TotientAsymptotic

def unitGridCell {N : ℕ} (m : Fin N → ℕ) : Set (Fin N → ℝ) :=
  Set.pi Set.univ (fun i => Set.Ico ((m i : ℝ)-1) (m i : ℝ))

lemma measurableSet_unitGridCell {N : ℕ} (m : Fin N → ℕ) :
    MeasurableSet (unitGridCell m) := by
  exact MeasurableSet.pi (Set.to_countable Set.univ) (fun _ _ => measurableSet_Ico)

lemma volume_unitGridCell {N : ℕ} (m : Fin N → ℕ) :
    volume (unitGridCell m) = 1 := by
  unfold unitGridCell
  rw [Real.volume_pi_Ico]
  simp

lemma unitGridCell_disjoint {N : ℕ} {m n : Fin N → ℕ} (hmn : m ≠ n) :
    Disjoint (unitGridCell m) (unitGridCell n) := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hmn
  apply Set.disjoint_left.mpr
  intro u hum hun
  have hm := hum i (Set.mem_univ _)
  have hn := hun i (Set.mem_univ _)
  rcases lt_or_gt_of_ne hi with hi | hi
  · have h : (m i : ℝ)+1 ≤ n i := by exact_mod_cast (show m i+1 ≤ n i by omega)
    linarith [hm.2, hn.1]
  · have h : (n i : ℝ)+1 ≤ m i := by exact_mod_cast (show n i+1 ≤ m i by omega)
    linarith [hn.2, hm.1]

def gridRegion {N : ℕ} (K : Finset (Fin N → ℕ)) : Set (Fin N → ℝ) :=
  ⋃ m ∈ K, unitGridCell m

lemma volume_gridRegion {N : ℕ} (K : Finset (Fin N → ℕ)) :
    volume (gridRegion K) = K.card := by
  unfold gridRegion
  rw [measure_biUnion_finset
    (fun m _ n _ hmn => unitGridCell_disjoint hmn)
    (fun m _ => measurableSet_unitGridCell m)]
  simp only [volume_unitGridCell, Finset.sum_const, nsmul_eq_mul, mul_one]

lemma gridRegion_volume_real {N : ℕ} (K : Finset (Fin N → ℕ)) :
    (volume (gridRegion K)).toReal = K.card := by
  rw [volume_gridRegion]
  simp

/-- A direct arithmetic-to-volume estimate on a finite union of prime boxes.
The later shell argument changes this grid region to the witness region. -/
theorem grid_prime_mass_volume_error (hford : FordUnitPrimeBoxInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ} (K : Finset (Fin N → ℕ)) (T : ℝ),
      (∀ m ∈ K, ∀ i, 1 ≤ m i ∧ T ≤ m i) →
      |gridPrimeMass K-(volume (gridRegion K)).toReal| ≤
        (volume (gridRegion K)).toReal*(Real.exp (C*N*Real.exp (-T))-1) := by
  simpa only [gridRegion_volume_real] using grid_prime_mass_error hford

end TotientAsymptotic

end

end OAI
