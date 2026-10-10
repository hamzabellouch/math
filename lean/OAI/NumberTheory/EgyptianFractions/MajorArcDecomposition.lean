import OAI.NumberTheory.EgyptianFractions.MajorArcApproximationBridge

namespace OAI
noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Problem337.MinorArc

/-- Reduced centers in the unit interval, with bounded denominator. -/
def centerSet (Q : ℕ) : Set ℚ :=
  {r | r.den ≤ Q ∧ 0 ≤ r.num ∧ r.num ≤ (r.den : ℤ)}

/-- The reduced centers form a genuinely finite set. -/
theorem finite_centerSet (Q : ℕ) : (centerSet Q).Finite := by
  let f : ℚ → ℤ × ℕ := fun r => (r.num, r.den)
  apply Set.Finite.of_injOn (f := f) (t :=
    Set.Icc (0 : ℤ) Q ×ˢ Set.Icc (1 : ℕ) Q)
  · intro r hr
    exact ⟨⟨hr.2.1, hr.2.2.trans (by exact_mod_cast hr.1)⟩,
      ⟨r.den_pos, hr.1⟩⟩
  · intro r _hr s _hs heq
    have hn : r.num = s.num := congrArg Prod.fst heq
    have hd : r.den = s.den := congrArg Prod.snd heq
    rw [← Rat.num_div_den r, ← Rat.num_div_den s, hn, hd]
  · exact (Set.finite_Icc _ _).prod (Set.finite_Icc _ _)

/-- The canonical finite indexing set of reduced centers, with duplicates removed. -/
def centers (Q : ℕ) : Finset ℚ := (finite_centerSet Q).toFinset

@[simp] theorem mem_centers {Q : ℕ} {r : ℚ} :
    r ∈ centers Q ↔ r.den ≤ Q ∧ 0 ≤ r.num ∧ r.num ≤ (r.den : ℤ) := by
  exact (finite_centerSet Q).mem_toFinset

/-- The exact finite reduced-center decomposition of the major region.
Clipping keeps both endpoint arcs at zero and one without any convention loss. -/
theorem majorArcs_unit_eq_centers_union {Q N : ℕ} (hN : 2 ≤ N) :
    majorArcs Q N ∩ Set.Icc (0 : ℝ) 1 =
      ⋃ r ∈ centers Q, arc N r ∩ Set.Icc (0 : ℝ) 1 := by
  ext x
  constructor
  · rintro ⟨⟨r, hrQ, hxr⟩, hx⟩
    obtain ⟨hlo, hhi⟩ := numerator_bounds_of_arc hN hx hxr
    exact Set.mem_iUnion.mpr ⟨r, Set.mem_iUnion.mpr
      ⟨mem_centers.mpr ⟨hrQ, hlo, hhi⟩, hxr, hx⟩⟩
  · intro hx
    obtain ⟨r, hr, hxr, hxunit⟩ := Set.mem_iUnion.mp hx |>.imp fun r =>
      fun h => Set.mem_iUnion.mp h
    exact ⟨⟨r, (mem_centers.mp hr).1, hxr⟩, hxunit⟩

/-- Distinct clipped reduced arcs are disjoint in the usual major-arc scale. -/
theorem centers_pairwiseDisjoint {Q N : ℕ} (hQN : 2 * Q < N) :
    Set.PairwiseDisjoint (↑(centers Q) : Set ℚ)
      (fun r => arc N r ∩ Set.Icc (0 : ℝ) 1) := by
  intro r hr s hs hrs
  have hrQ := (mem_centers.mp hr).1
  have hsQ := (mem_centers.mp hs).1
  exact Disjoint.mono Set.inter_subset_left Set.inter_subset_left
    (arc_disjoint hrs (by omega))

/-- Exact integration over major arcs is a finite sum over reduced centers.
The only analytic premise is integrability of the actual integrand on `[0,1]`. -/
theorem integral_majorArcs_eq_sum {Q N : ℕ} (hN : 2 ≤ N) (hQN : 2 * Q < N)
    (f : ℝ → ℂ) (hf : IntegrableOn f (Set.Icc (0 : ℝ) 1)) :
    (∫ x in majorArcs Q N ∩ Set.Icc (0 : ℝ) 1, f x) =
      ∑ r ∈ centers Q, ∫ x in arc N r ∩ Set.Icc (0 : ℝ) 1, f x := by
  rw [majorArcs_unit_eq_centers_union hN]
  apply integral_biUnion_finset
  · intro r _hr
    exact (isClosed_arc N r).measurableSet.inter measurableSet_Icc
  · exact centers_pairwiseDisjoint hQN
  · intro r _hr
    exact hf.mono_set Set.inter_subset_right

/-- The whole interval integral splits into the explicit reduced major-arc sum
and its minor complement, with no implicit endpoint or overlap error. -/
theorem integral_unit_eq_major_sum_add_minor {Q N : ℕ}
    (hN : 2 ≤ N) (hQN : 2 * Q < N)
    (f : ℝ → ℂ) (hf : IntegrableOn f (Set.Icc (0 : ℝ) 1)) :
    (∫ x in Set.Icc (0 : ℝ) 1, f x) =
      (∑ r ∈ centers Q, ∫ x in arc N r ∩ Set.Icc (0 : ℝ) 1, f x) +
      ∫ x in Set.Icc (0 : ℝ) 1 \ majorArcs Q N, f x := by
  have hsplit := integral_inter_add_sdiff (measurableSet_majorArcs Q N) hf
  rw [Set.inter_comm, integral_majorArcs_eq_sum hN hQN f hf] at hsplit
  exact hsplit.symm

/-- The same exact decomposition using the finite major region in the
prime/AP approximation API. -/
theorem integral_majorArcUnion_unit_eq_sum {Q N : ℕ}
    (hN : 2 ≤ N) (hQN : 2 * Q < N)
    (f : ℝ → ℂ) (hf : IntegrableOn f (Set.Icc (0 : ℝ) 1)) :
    (∫ x in ThreePrimeAnalysis.majorArcUnion Q (1 / (N : ℝ)) ∩
      Set.Icc (0 : ℝ) 1, f x) =
      ∑ r ∈ centers Q, ∫ x in arc N r ∩ Set.Icc (0 : ℝ) 1, f x := by
  rw [← majorArcs_unit_eq_majorArcUnion_unit hN]
  exact integral_majorArcs_eq_sum hN hQN f hf

end Problem337.MinorArc

end

end OAI
