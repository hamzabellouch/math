import OAI.NumberTheory.TotientAsymptotic.PrimeBoxGeometry
import OAI.NumberTheory.TotientAsymptotic.PrefixRelaxation

namespace OAI

/-! Finite grids covering the actual arithmetic prefix fibers. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def bandGrid (x : ℝ) (H : ℕ) : Finset (Fin (R x H) → ℕ) :=
  (Fintype.piFinset (fun i : Fin (R x H) =>
    Finset.Icc 1 (⌊(11/10 : ℝ)*bandScale x (i.val+1)⌋₊+1))).filter
      (fun m => ∀ i, (9/10 : ℝ)*bandScale x (i.val+1) ≤ m i)

lemma bandGrid_bounds {x : ℝ} {H : ℕ} {m : Fin (R x H) → ℕ} (hm : m ∈ bandGrid x H)
    (i : Fin (R x H)) : 1 ≤ m i ∧ (9/10 : ℝ)*bandScale x (i.val+1) ≤ m i := by
  obtain ⟨hm, hlo⟩ := Finset.mem_filter.mp hm
  exact ⟨(Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hm i)).1, hlo i⟩

lemma prefixBandRegion_covered (x : ℝ) (H : ℕ) :
    prefixBandRegion x H ⊆ gridRegion (bandGrid x H) := by
  intro u hu
  let m : Fin (R x H) → ℕ := fun i => ⌊u i⌋₊+1
  have h0 (i) : 0 ≤ u i :=
    (mul_nonneg (by norm_num) (bandScale_nonneg x (i.val+1))).trans (hu i).1
  have hc : u ∈ unitGridCell m := by
    intro i _
    dsimp [m]
    rw [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    exact ⟨Nat.floor_le (h0 i), Nat.lt_floor_add_one (u i)⟩
  have hm : m ∈ bandGrid x H := by
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (fun i => ?_), ?_⟩
    · apply Finset.mem_Icc.mpr
      refine ⟨by dsimp [m]; omega, ?_⟩
      exact Nat.add_le_add_right (Nat.floor_mono (hu i).2) 1
    · intro i
      exact (hu i).1.trans (hc i (Set.mem_univ _)).2.le
  exact Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr ⟨hm, hc⟩⟩

def bandedWitnessRegion (x : ℝ) (H d : ℕ) : Set (Fin (R x H) → ℝ) :=
  prefixBandRegion x H ∩ ⋃ η ∈ witnesses H (theta x) d, perturbedTailPrefixRegion x H η

lemma prefixDatum_iff_prime_region {x : ℝ} {H d : ℕ}
    (hPH : P H < H) (hHm : H ≤ m x) (p : Fin (R x H) → ℕ) :
    IsPrefixDatum x H ⟨p,d⟩ ↔
      (∀ i, (p i).Prime) ∧ primePrefixCoord p ∈ bandedWitnessRegion x H d := by
  rw [prefixDatum_iff_banded_region hPH hHm]
  simp only [bandedWitnessRegion, Set.mem_inter_iff, Set.mem_iUnion]
  constructor
  · rintro ⟨hp, η, hη, hu⟩
    exact ⟨fun i => (hp i).1, (fun i => (hp i).2), η, hη, hu⟩
  · rintro ⟨hp, hb, η, hη, hu⟩
    exact ⟨fun i => ⟨hp i, hb i⟩, η, hη, hu⟩

/-- The actual finite prefix fiber is a restricted prime-box grid, with one
copy of each prefix even if several witnesses permit it. -/
theorem prefixPrimeFiber_eq_grid {x : ℝ} {H d : ℕ}
    (hPH : P H < H) (hHm : H ≤ m x) :
    prefixPrimeFiber x H d = (gridPrimeTuples (bandGrid x H)).filter
      (fun p => primePrefixCoord p ∈ bandedWitnessRegion x H d) := by
  ext p
  rw [mem_prefixPrimeFiber, prefixDatum_iff_prime_region hPH hHm,
    Finset.mem_filter, mem_gridPrimeTuples_iff]
  constructor
  · rintro ⟨hp, hu⟩
    exact ⟨⟨hp, prefixBandRegion_covered x H hu.1⟩, hu⟩
  · rintro ⟨⟨hp, _⟩, hu⟩
    exact ⟨hp, hu⟩

/-- Exact conversion of the arithmetic mass to the bounded grid regions.
All subsequent estimates act on these regions, not on a count of witnesses. -/
theorem mass_eq_banded_grid_sum {x : ℝ} {H : ℕ}
    (hPH : P H < H) (hHm : H ≤ m x) (hs : theta x ∈ Set.Ico (0 : ℝ) 1)
    (f : ℝ → ℝ) :
    M x H f = ∑ d ∈ Finset.Icc 1 (tailValueBound H), f ((ell d : ℝ)/d)/d *
      gridRestrictedPrimeMass (bandGrid x H) (bandedWitnessRegion x H d) := by
  rw [mass_eq_finite_tail_sum hPH hHm hs]
  apply Finset.sum_congr rfl
  intro d _
  rw [prefixPrimeFiber_eq_grid hPH hHm]
  rfl

end TotientAsymptotic

end

end OAI
