import OAI.NumberTheory.EgyptianFractions.MinorArcApproximation

namespace OAI
noncomputable section

namespace Problem337.MinorArc

/-- A major arc with all integer translates retained. Restricting this set
to a unit interval handles the arc crossing the endpoint zero without loss. -/
def periodicArc (N : ℕ) (r : ℚ) : Set ℝ :=
  {x | ∃ k : ℤ, x ∈ arc N (r + k)}

theorem mem_periodicArc_iff {N : ℕ} {r : ℚ} {x : ℝ} :
    x ∈ periodicArc N r ↔
      ∃ k : ℤ, |x - (r : ℝ) - k| ≤ 1 / ((r.den : ℝ) * N) := by
  simp only [periodicArc, arc, Set.mem_ofPred_eq, Rat.add_intCast_den,
    Rat.cast_add, Rat.cast_intCast, sub_add_eq_sub_sub]

/-- Normalized rational centers remain different under every pair of integer
translates. This is where the half-open convention at the unit endpoints matters. -/
theorem normalized_centers_translate_ne {r s : ℚ}
    (hr : r ∈ Set.Ico (0 : ℚ) 1) (hs : s ∈ Set.Ico (0 : ℚ) 1)
    (hrs : r ≠ s) (k l : ℤ) : r + k ≠ s + l := by
  intro heq
  have hfract := congrArg Int.fract heq
  rw [Int.fract_add_intCast, Int.fract_add_intCast,
    Int.fract_eq_self.mpr hr, Int.fract_eq_self.mpr hs] at hfract
  exact hrs hfract

/-- Reciprocal-product separation on the circle, not merely on the real line. -/
theorem periodic_rational_separation {r s : ℚ}
    (hr : r ∈ Set.Ico (0 : ℚ) 1) (hs : s ∈ Set.Ico (0 : ℚ) 1)
    (hrs : r ≠ s) (k : ℤ) :
    1 / ((r.den : ℝ) * s.den) ≤ |(r : ℝ) - s - k| := by
  have hne : r ≠ s + k := by
    simpa only [Int.cast_zero, add_zero] using
      normalized_centers_translate_ne hr hs hrs 0 k
  simpa only [Rat.add_intCast_den, Rat.cast_add, Rat.cast_intCast,
    sub_add_eq_sub_sub] using rational_separation hne

/-- The canonical real-line disjointness theorem also gives disjoint periodic
arcs, provided the normalized centers are different. -/
theorem periodicArc_disjoint {r s : ℚ}
    (hr : r ∈ Set.Ico (0 : ℚ) 1) (hs : s ∈ Set.Ico (0 : ℚ) 1)
    (hrs : r ≠ s) {N : ℕ} (hN : r.den + s.den < N) :
    Disjoint (periodicArc N r) (periodicArc N s) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨k, hk⟩ ⟨l, hl⟩
  have hdis := arc_disjoint (normalized_centers_translate_ne hr hs hrs k l)
    (by simpa only [Rat.add_intCast_den] using hN)
  exact Set.disjoint_left.mp hdis hk hl

/-- Every point has at most one normalized major-arc center in the usual
`2Q < N` disjointness window, including points near the unit endpoints. -/
theorem periodic_major_arc_unique {Q N : ℕ} (hQN : 2 * Q < N) {x : ℝ}
    {r s : ℚ} (hr : r ∈ Set.Ico (0 : ℚ) 1) (hs : s ∈ Set.Ico (0 : ℚ) 1)
    (hrQ : r.den ≤ Q) (hsQ : s.den ≤ Q)
    (hxr : x ∈ periodicArc N r) (hxs : x ∈ periodicArc N s) : r = s := by
  by_contra hrs
  exact Set.disjoint_left.mp (periodicArc_disjoint hr hs hrs (by omega)) hxr hxs

/-- Integer translations preserve reduced denominator. -/
theorem fract_den (r : ℚ) : (Int.fract r).den = r.den := by
  simp only [Int.fract, Rat.sub_intCast_den]

/-- The all-rational major arcs have an exact normalized periodic presentation.
In particular, no extra endpoint arc may be discarded at zero or one. -/
theorem majorArcs_eq_normalized_periodic (Q N : ℕ) :
    majorArcs Q N =
      {x | ∃ r : ℚ, r ∈ Set.Ico (0 : ℚ) 1 ∧ r.den ≤ Q ∧ x ∈ periodicArc N r} := by
  ext x
  constructor
  · rintro ⟨r, hrQ, hxr⟩
    refine ⟨Int.fract r, ⟨Int.fract_nonneg r, Int.fract_lt_one r⟩, ?_, ?_⟩
    · simpa only [fract_den] using hrQ
    · refine ⟨⌊r⌋, ?_⟩
      simpa only [Int.fract_add_floor] using hxr
  · rintro ⟨r, hr, hrQ, k, hk⟩
    refine ⟨r + k, ?_, hk⟩
    simpa only [Rat.add_intCast_den] using hrQ

/-- Periodic arcs are measurable countable unions of closed real intervals. -/
theorem measurableSet_periodicArc (N : ℕ) (r : ℚ) :
    MeasurableSet (periodicArc N r) := by
  have heq : periodicArc N r = ⋃ k : ℤ, arc N (r + k) := by
    ext x
    simp only [periodicArc, Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [heq]
  apply MeasurableSet.iUnion
  intro k
  exact (isClosed_le (continuous_id.sub continuous_const).abs
    continuous_const).measurableSet

/-- Bounded-denominator, half-open normalized centers form a finite set. -/
theorem finite_normalized_centers (Q : ℕ) :
    {r : ℚ | r ∈ Set.Ico (0 : ℚ) 1 ∧ r.den ≤ Q}.Finite := by
  classical
  let F := ((Finset.range (Q + 1)).product (Finset.range (Q + 1))).image
    (fun p : ℕ × ℕ => (p.1 : ℚ) / p.2)
  apply F.finite_toSet.subset
  rintro r ⟨hr, hrQ⟩
  have hnum0 : 0 ≤ r.num := Rat.num_nonneg.mpr hr.1
  have hcast : (r.num.toNat : ℚ) = r.num := by
    exact_mod_cast Int.toNat_of_nonneg hnum0
  have hden : (0 : ℚ) < r.den := by exact_mod_cast r.den_pos
  have hnumlt : (r.num : ℚ) < r.den := by
    apply (div_lt_one hden).mp
    simpa only [Rat.num_div_den] using hr.2
  have hnumN : r.num.toNat < r.den := by
    rw [← hcast] at hnumlt
    exact_mod_cast hnumlt
  apply Finset.mem_image.mpr
  refine ⟨(r.num.toNat, r.den), ?_, ?_⟩
  · apply Finset.mem_product.mpr
    constructor <;> apply Finset.mem_range.mpr <;> omega
  · simpa only [hcast] using r.num_div_den

/-- A finite, endpoint-safe index type for major-arc integration. -/
def normalizedCenters (Q : ℕ) : Finset ℚ :=
  (finite_normalized_centers Q).toFinset

theorem mem_normalizedCenters {Q : ℕ} {r : ℚ} :
    r ∈ normalizedCenters Q ↔ r ∈ Set.Ico (0 : ℚ) 1 ∧ r.den ≤ Q := by
  simp only [normalizedCenters, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]

/-- Exact finite union, with the zero-center's wrap-around arc retained. -/
theorem majorArcs_eq_iUnion_periodic (Q N : ℕ) :
    majorArcs Q N = ⋃ r ∈ normalizedCenters Q, periodicArc N r := by
  rw [majorArcs_eq_normalized_periodic]
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, mem_normalizedCenters]
  tauto

/-- The finite periodic presentation is pairwise disjoint in the standard
major-arc separation window. -/
theorem pairwiseDisjoint_periodicArcs {Q N : ℕ} (hQN : 2 * Q < N) :
    (normalizedCenters Q : Set ℚ).PairwiseDisjoint (periodicArc N) := by
  intro r hr s hs hrs
  obtain ⟨hr, hrQ⟩ := mem_normalizedCenters.mp hr
  obtain ⟨hs, hsQ⟩ := mem_normalizedCenters.mp hs
  exact periodicArc_disjoint hr hs hrs (by omega)

end Problem337.MinorArc

end

end OAI
