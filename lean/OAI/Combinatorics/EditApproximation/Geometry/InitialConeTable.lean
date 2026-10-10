import OAI.Combinatorics.EditApproximation.Geometry.InitialConeGrid

namespace OAI

/-!
# The finite global initial-cone table

Every center is a valid target state. The family includes the zero seed
centers and precisely the eligible grid centers at the finite dyadic scales.
The constant fallback is above a witnessed cone on a good seed.
-/

namespace EditApproximation

def initialConeCenters {n : ℕ} (N P : ℕ) (A : ℚ) (U : TargetInterval n → ℕ) :
    List (TargetInterval n) :=
  (targetStates n).filter (fun r => decide (U r = 0)) ++
  (dyadicScales N).flatMap (fun b =>
    (targetStates n).filter (fun r => decide
      (seedGridSpacing b P ∣ r.lo ∧ seedGridSpacing b P ∣ r.hi ∧
        (b : ℚ) / 2 ≤ U r ∧ (U r : ℚ) ≤ 4 * A * b)))

def globalInitialConeTable {α : Type*} (source target : List α)
    (U : TargetInterval target.length → ℕ) (N P F : ℕ) (A a : ℚ)
    (q : TargetInterval target.length) : ℚ :=
  rationalMinimum ((32 * F + 1) * N)
    ((initialConeCenters N P A U).map (initialConeValue source target U a (32 * F) q))

theorem rationalMinimum_le_member (fallback : ℚ) (values : List ℚ)
    {v : ℚ} (hv : v ∈ values) : rationalMinimum fallback values ≤ v := by
  induction values with
  | nil => simp at hv
  | cons x rest ih =>
    rcases List.mem_cons.mp hv with rfl | hrest
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih hrest)

theorem le_rationalMinimum_iff (lower fallback : ℚ) (values : List ℚ) :
    lower ≤ rationalMinimum fallback values ↔ lower ≤ fallback ∧ ∀ v ∈ values, lower ≤ v := by
  induction values with
  | nil => simp [rationalMinimum]
  | cons v rest ih =>
    simp only [rationalMinimum, le_min_iff, ih, List.mem_cons, forall_eq_or_imp]
    tauto

theorem initialConeCenters_mem_zero {n N P : ℕ} {A : ℚ} (U : TargetInterval n → ℕ)
    (r : TargetInterval n) (hzero : U r = 0) : r ∈ initialConeCenters N P A U := by
  apply List.mem_append_left
  exact List.mem_filter.mpr ⟨targetStates_complete n r, by simpa using hzero⟩

theorem initialConeCenters_mem_grid {n N P b : ℕ} {A : ℚ}
    (U : TargetInterval n → ℕ) (r : TargetInterval n) (hb : b ∈ dyadicScales N)
    (hr : seedGridSpacing b P ∣ r.lo ∧ seedGridSpacing b P ∣ r.hi ∧
      (b : ℚ) / 2 ≤ U r ∧ (U r : ℚ) ≤ 4 * A * b) :
    r ∈ initialConeCenters N P A U := by
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨b, hb,
    List.mem_filter.mpr ⟨targetStates_complete n r, by simpa using hr⟩⟩

theorem globalInitialConeTable_bounds {α : Type*} (source target : List α)
    (U : TargetInterval target.length → ℕ) (N P F : ℕ) (A a : ℚ)
    (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A) (ha : 1 ≤ a)
    (hfactor : A ≤ a * F)
    (hcostN : ∀ r, stateEditCost source target r ≤ N)
    (hseed : ∀ r, stateEditCost source target r ≤ U r ∧
      (U r : ℚ) ≤ A * stateEditCost source target r)
    (q : TargetInterval target.length) :
    max ((stateEditCost source target q : ℚ) / a) |rationalStateGap source target q| ≤
      globalInitialConeTable source target U N P F A a q ∧
    globalInitialConeTable source target U N P F A a q ≤
      2 * F * stateEditCost source target q := by
  have hFQ : (1 : ℚ) ≤ F := by exact_mod_cast hF
  have hgap : |rationalStateGap source target q| ≤ (stateEditCost source target q : ℚ) := by
    have h := stateEditCost_length_lower source target q
    rw [← rationalStateGap_cast] at h
    exact_mod_cast h
  have hcost : (stateEditCost source target q : ℚ) ≤ N := by exact_mod_cast hcostN q
  have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg _
  constructor
  · apply (le_rationalMinimum_iff _ _ _).2
    constructor
    · have hdiv : (stateEditCost source target q : ℚ) / a ≤ stateEditCost source target q := by
        apply (div_le_iff₀ (by linarith : 0 < a)).2
        have hc0 : (0 : ℚ) ≤ stateEditCost source target q := Nat.cast_nonneg _
        nlinarith
      apply max_le <;> nlinarith
    · intro v hv
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hv
      exact initialConeValue_actual_lower source target U a (32 * F) q r ha
        (by linarith) (hseed r).1
  · by_cases hc : stateEditCost source target q = 0
    · have hU : U q = 0 := by
        have h := (hseed q).2
        rw [hc, Nat.cast_zero, mul_zero] at h
        exact_mod_cast (le_antisymm h (Nat.cast_nonneg _))
      have hgap0 : rationalStateGap source target q = 0 := by
        rw [hc, Nat.cast_zero] at hgap
        exact abs_eq_zero.mp (le_antisymm hgap (abs_nonneg _))
      have hmem := initialConeCenters_mem_zero (N := N) (P := P) (A := A) U q hU
      have hvalue := rationalMinimum_le_member ((32 * F + 1) * N)
        ((initialConeCenters N P A U).map (initialConeValue source target U a (32 * F) q))
        (List.mem_map.mpr ⟨q, hmem, rfl⟩)
      simpa only [globalInitialConeTable, initialConeValue, hU, hgap0,
        scaledSeedValue_zero, targetEndpointDistance, Nat.dist_self, zero_add,
        Nat.cast_zero, mul_zero, add_zero, hc] using hvalue
    · obtain ⟨b, hb, r, hgridLo, hgridHi, hlow, hupp, hcone⟩ :=
        rounded_initial_cone_witness source target U N P F A a q (by omega)
          (hcostN q) hP hF hA ha hseed hfactor
      have hmem := initialConeCenters_mem_grid U r hb ⟨hgridLo, hgridHi, hlow, hupp⟩
      exact (rationalMinimum_le_member _ _ (List.mem_map.mpr ⟨r, hmem, rfl⟩)).trans hcone

theorem targetEndpointDistance_triangle {n : ℕ} (q q' r : TargetInterval n) :
    targetEndpointDistance q r ≤ targetEndpointDistance q' r + targetEndpointDistance q q' := by
  unfold targetEndpointDistance Nat.dist
  omega

theorem globalInitialConeTable_spatial {α : Type*} (source target : List α)
    (U : TargetInterval target.length → ℕ) (N P F : ℕ) (A a : ℚ)
    (q q' : TargetInterval target.length) :
    globalInitialConeTable source target U N P F A a q ≤
      globalInitialConeTable source target U N P F A a q' +
        (32 * F : ℚ) * targetEndpointDistance q q' := by
  have hcast (query : TargetInterval target.length) :
      (globalInitialConeTable source target U N P F A a query : ℝ) =
        finiteMinimum (((32 * F + 1) * N : ℚ) : ℝ)
          ((initialConeCenters N P A U).map
            fun r => (initialConeValue source target U a (32 * F) query r : ℝ)) := by
    rw [globalInitialConeTable, rationalMinimum_cast]
    simp only [List.map_map, Function.comp_def]
  have h := finiteMinimum_map_spatial (initialConeCenters N P A U)
    (((32 * F + 1) * N : ℚ) : ℝ) (((32 * F + 1) * N : ℚ) : ℝ)
    (((32 * F : ℚ) * targetEndpointDistance q q' : ℚ) : ℝ)
    (fun r => (initialConeValue source target U a (32 * F) q r : ℝ))
    (fun r => (initialConeValue source target U a (32 * F) q' r : ℝ))
    (le_add_of_nonneg_right (by positivity)) (by
      intro r hr
      have htri : (targetEndpointDistance q r : ℚ) ≤
          targetEndpointDistance q' r + targetEndpointDistance q q' := by
        exact_mod_cast targetEndpointDistance_triangle q q' r
      have hmult := mul_le_mul_of_nonneg_left htri (by positivity : (0 : ℚ) ≤ 32 * F)
      have hcone : initialConeValue source target U a (32 * F) q r ≤
          initialConeValue source target U a (32 * F) q' r +
            (32 * F : ℚ) * targetEndpointDistance q q' := by
        unfold initialConeValue
        linarith
      exact_mod_cast hcone)
  rw [← hcast q, ← hcast q'] at h
  exact_mod_cast h

end EditApproximation

end OAI
