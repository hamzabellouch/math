import OAI.Combinatorics.EditApproximation.Geometry.InitialConeTable
import OAI.Combinatorics.EditApproximation.Geometry.LocalGrid
import OAI.Combinatorics.EditApproximation.Geometry.ConeLocality
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-!
# Exact local evaluation of the initial cones

The local implementation enumerates only the stated dyadic scale interval
and the grid square about the query. Zero cones are never searched at a
positive seed query. Equality with the global family is proved on a good
seed; the local program is finite on every input table.
-/

namespace EditApproximation





theorem rationalMinimum_le_fallback (fallback : ℚ) (values : List ℚ) :
    rationalMinimum fallback values ≤ fallback := by
  induction values with
  | nil => rfl
  | cons v rest ih => exact (min_le_right _ _).trans ih

theorem rationalMinimum_attained (fallback : ℚ) (values : List ℚ) :
    rationalMinimum fallback values = fallback ∨ rationalMinimum fallback values ∈ values := by
  induction values with
  | nil => exact Or.inl rfl
  | cons v rest ih =>
    by_cases h : v ≤ rationalMinimum fallback rest
    · exact Or.inr (by simp only [rationalMinimum, min_eq_left h, List.mem_cons, true_or])
    · rw [rationalMinimum, min_eq_right (le_of_not_ge h)]
      exact ih.imp_right (fun hmem => List.mem_cons.mpr (Or.inr hmem))

theorem localTargetStates_on_grid {n g radius : ℕ} (q r : TargetInterval n)
    (hmem : r ∈ localTargetStates n g radius q) : g ∣ r.lo ∧ g ∣ r.hi := by
  obtain ⟨lo, hlo, hrest⟩ := List.mem_flatMap.mp hmem
  obtain ⟨hi, hhi, hmake⟩ := List.mem_filterMap.mp hrest
  unfold makeTargetState at hmake
  split at hmake
  · cases Option.some.inj hmake
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hlo
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hhi
    exact ⟨dvd_mul_right _ _, dvd_mul_right _ _⟩
  · contradiction

theorem localInitialConeCenters_subset {n N P : ℕ} {A : ℚ}
    (U : TargetInterval n → ℕ) (q : TargetInterval n) :
    ∀ r ∈ localInitialConeCenters N P A U q, r ∈ initialConeCenters N P A U := by
  intro r hr
  obtain ⟨b, hb, hgrid⟩ := List.mem_flatMap.mp hr
  have hscale := (List.mem_filter.mp hb).1
  have hlocal := (List.mem_filter.mp hgrid).1
  have heligible : (b : ℚ) / 2 ≤ U r ∧ (U r : ℚ) ≤ 4 * A * b := by
    simpa using (List.mem_filter.mp hgrid).2
  have hdiv := localTargetStates_on_grid q r hlocal
  exact initialConeCenters_mem_grid U r hscale ⟨hdiv.1, hdiv.2, heligible⟩

theorem localInitialConeTable_eq_global {α : Type*} (source target : List α)
    (U : TargetInterval target.length → ℕ) (N P F : ℕ) (A a : ℚ)
    (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A) (ha : 1 ≤ a)
    (hfactor : A ≤ a * F)
    (hcostN : ∀ r, stateEditCost source target r ≤ N)
    (hseed : ∀ r, stateEditCost source target r ≤ U r ∧
      (U r : ℚ) ≤ A * stateEditCost source target r)
    (q : TargetInterval target.length) :
    localInitialConeTable source target U N P F A a q =
      globalInitialConeTable source target U N P F A a q := by
  let global := globalInitialConeTable source target U N P F A a q
  have hbounds := globalInitialConeTable_bounds source target U N P F A a
    hP hF hA ha hfactor hcostN hseed q
  have hFQ : (0 : ℚ) < F := by exact_mod_cast (by omega : 0 < F)
  have hnonneg : 0 ≤ global := (abs_nonneg _).trans ((le_max_right _ _).trans hbounds.1)
  by_cases hzero : U q = 0
  · have hc : stateEditCost source target q = 0 := by have h := (hseed q).1; omega
    have hg : global = 0 := by
      have hupper := hbounds.2
      rw [hc, Nat.cast_zero, mul_zero] at hupper
      exact le_antisymm hupper hnonneg
    simpa only [localInitialConeTable, ite_true, hzero] using hg.symm
  have hc : (0 : ℚ) < stateEditCost source target q := by
    have h := (hseed q).2
    have hU : (0 : ℚ) < U q := by exact_mod_cast (by omega : 0 < U q)
    by_contra hn
    have hc0 : (stateEditCost source target q : ℚ) = 0 :=
      le_antisymm (le_of_not_gt hn) (Nat.cast_nonneg _)
    rw [hc0, mul_zero] at h
    linarith
  rw [localInitialConeTable, ite_eq_right hzero]
  apply le_antisymm
  · rcases rationalMinimum_attained ((32 * F + 1) * N)
      ((initialConeCenters N P A U).map
        (initialConeValue source target U a (32 * F) q)) with hfallback | hmember
    · exact (rationalMinimum_le_fallback _ _).trans_eq hfallback.symm
    · obtain ⟨r, hr, hvalue⟩ := List.mem_map.mp hmember
      have hconeUpper : initialConeValue source target U a (32 * F) q r ≤
          2 * F * stateEditCost source target q := hvalue.le.trans hbounds.2
      have hconeLower : (32 * F : ℚ) * targetEndpointDistance q r ≤
          initialConeValue source target U a (32 * F) q r := by
        unfold initialConeValue scaledSeedValue
        have hscaled : (0 : ℚ) ≤ max (⌈(U r : ℚ) / a⌉₊ : ℚ)
            |rationalStateGap source target r| := (abs_nonneg _).trans (le_max_right _ _)
        linarith
      rcases List.mem_append.mp hr with hzeroCenter | hgridCenter
      · have hUr : U r = 0 := by simpa using (List.mem_filter.mp hzeroCenter).2
        have hcr : stateEditCost source target r = 0 := by have h := (hseed r).1; omega
        have hdist := stateEditCost_distance_abs source target q r
        rw [hcr, Nat.cast_zero, sub_zero, abs_of_pos hc] at hdist
        have hmul := mul_le_mul_of_nonneg_left hdist (by positivity : (0 : ℚ) ≤ 32 * F)
        nlinarith
      · obtain ⟨b, hb, helig⟩ := List.mem_flatMap.mp hgridCenter
        have heligible : seedGridSpacing b P ∣ r.lo ∧ seedGridSpacing b P ∣ r.hi ∧
            (b : ℚ) / 2 ≤ U r ∧ (U r : ℚ) ≤ 4 * A * b := by
          simpa using (List.mem_filter.mp helig).2
        have hlocality := initial_cone_locality_numeric hc hA hFQ (Nat.cast_nonneg b)
          ⟨by exact_mod_cast (hseed q).1, (hseed q).2⟩
          ⟨by exact_mod_cast (hseed r).1, (hseed r).2⟩
          (stateEditCost_distance_abs source target q r) heligible.2.2 hconeLower hconeUpper
        have hdist : targetEndpointDistance q r ≤ U q := by exact_mod_cast hlocality.2.2.2.2
        have hmemLocal : r ∈ localInitialConeCenters N P A U q := by
          apply List.mem_flatMap.mpr
          refine ⟨b, List.mem_filter.mpr ⟨hb, ?_⟩, List.mem_filter.mpr ⟨?_, ?_⟩⟩
          · simpa using ⟨hlocality.2.2.1, hlocality.2.2.2.1⟩
          · apply localTargetStates_complete (by unfold seedGridSpacing; omega) q r
              (by unfold targetEndpointDistance at hdist; omega)
              (by unfold targetEndpointDistance at hdist; omega)
              ⟨heligible.1, heligible.2.1⟩
          · simpa using heligible.2.2
        exact (rationalMinimum_le_member _ _
          (List.mem_map.mpr ⟨r, hmemLocal, rfl⟩)).trans_eq hvalue
  · apply (le_rationalMinimum_iff _ _ _).2
    constructor
    · exact rationalMinimum_le_fallback _ _
    · intro v hv
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hv
      exact rationalMinimum_le_member _ _ (List.mem_map.mpr
        ⟨r, localInitialConeCenters_subset U q r hr, rfl⟩)

end EditApproximation

end OAI
