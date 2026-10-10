import OAI.NumberTheory.EgyptianFractions.MinorArcApproximation

namespace OAI
noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Problem337.MinorArc

/-- Each individual rational arc is closed. -/
theorem isClosed_arc (N : ℕ) (r : ℚ) : IsClosed (arc N r) := by
  exact isClosed_le (continuous_id.sub continuous_const).abs continuous_const

/-- The major arcs form a measurable set, since the rational centers are countable. -/
theorem measurableSet_majorArcs (Q N : ℕ) : MeasurableSet (majorArcs Q N) := by
  have heq : majorArcs Q N = ⋃ r : ℚ, ⋃ (_ : r.den ≤ Q), arc N r := by
    ext x
    simp [majorArcs]
  rw [heq]
  exact MeasurableSet.iUnion fun r => MeasurableSet.iUnion fun _ =>
    (isClosed_arc N r).measurableSet

/-- A rational arc written without requiring its displayed fraction to be reduced. -/
def rationalWindow (N q a : ℕ) : Set ℝ :=
  Set.Icc ((a : ℝ) / q - 1 / ((q : ℝ) * N))
    ((a : ℝ) / q + 1 / ((q : ℝ) * N))

/-- At scales at least two, a major arc meeting the unit interval has its
reduced numerator between zero and its denominator. -/
theorem numerator_bounds_of_arc {N : ℕ} (hN : 2 ≤ N) {r : ℚ} {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hxr : x ∈ arc N r) :
    0 ≤ r.num ∧ r.num ≤ (r.den : ℤ) := by
  have hd : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNpos : (0 : ℝ) < N := by linarith
  have herr : |x * r.den - (r.num : ℝ)| ≤ 1 / (N : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hxr hd.le
    change |x - (r : ℝ)| * r.den ≤ (1 / ((r.den : ℝ) * N)) * r.den at hh
    rw [← abs_of_pos hd, ← abs_mul] at hh
    have heq : (x - (r : ℝ)) * r.den = x * r.den - (r.num : ℝ) := by
      rw [Rat.cast_def]
      field_simp
    rw [heq] at hh
    convert hh using 1
    field_simp
  have hless : 1 / (N : ℝ) < 1 := (div_lt_one hNpos).mpr hn
  have hlow : (-1 : ℝ) < r.num := by
    have hab := (abs_le.mp herr).2
    have hx0 := mul_nonneg hx.1 hd.le
    linarith
  have hupp : (r.num : ℝ) < (r.den : ℝ) + 1 := by
    have hab := (abs_le.mp herr).1
    have hx1 := mul_le_mul_of_nonneg_right hx.2 hd.le
    linarith
  have hlowZ : (-1 : ℤ) < r.num := by exact_mod_cast hlow
  have huppZ : r.num < (r.den : ℤ) + 1 := by exact_mod_cast hupp
  omega

/-- An explicit finite cover, retaining the natural numerator and denominator
needed to sum the arc lengths. -/
theorem majorArcs_unit_subset {Q N : ℕ} (hN : 2 ≤ N) :
    majorArcs Q N ∩ Set.Icc (0 : ℝ) 1 ⊆
      ⋃ q ∈ Finset.Icc 1 Q, ⋃ a ∈ Finset.range (q + 1), rationalWindow N q a := by
  rintro x ⟨⟨r, hrQ, hxr⟩, hx⟩
  obtain ⟨hnum0, hnumden⟩ := numerator_bounds_of_arc hN hx hxr
  have hnum : ((r.num.toNat : ℕ) : ℤ) = r.num := Int.toNat_of_nonneg hnum0
  have hnumR : (r.num.toNat : ℝ) = r.num := by exact_mod_cast hnum
  have hnumle : r.num.toNat ≤ r.den := by omega
  refine Set.mem_iUnion.mpr ⟨r.den, Set.mem_iUnion.mpr ⟨?_,
    Set.mem_iUnion.mpr ⟨r.num.toNat, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩⟩⟩
  · exact Finset.mem_Icc.mpr ⟨r.den_pos, hrQ⟩
  · exact Finset.mem_range.mpr (by omega)
  · change _ ≤ x ∧ x ≤ _
    change |x - (r : ℝ)| ≤ 1 / ((r.den : ℝ) * N) at hxr
    rw [Rat.cast_def] at hxr
    rw [hnumR]
    obtain ⟨hlow, hhigh⟩ := abs_le.mp hxr
    constructor <;> linarith

/-- The length of one displayed rational window. -/
theorem volume_rationalWindow (N q a : ℕ) :
    volume (rationalWindow N q a) = ENNReal.ofReal (2 / ((q : ℝ) * N)) := by
  rw [rationalWindow, Real.volume_Icc]
  congr 1
  ring

/-- The contribution from one positive denominator is at most `4/N`. -/
theorem volume_windows_fixed_den_le (N q : ℕ) (hq : 1 ≤ q) :
    volume (⋃ a ∈ Finset.range (q + 1), rationalWindow N q a) ≤
      ENNReal.ofReal (4 / (N : ℝ)) := by
  calc
    _ ≤ ∑ a ∈ Finset.range (q + 1), volume (rationalWindow N q a) :=
      measure_biUnion_finset_le _ _
    _ = ENNReal.ofReal ((q + 1 : ℕ) * (2 / ((q : ℝ) * N))) := by
      simp_rw [volume_rationalWindow]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
      simp
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      by_cases hN : N = 0
      · simp [hN]
      have hn : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
      have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
      have hqpos : (0 : ℝ) < q := by linarith
      push_cast
      field_simp
      nlinarith

/-- A quantitative major-arc volume bound on the unit interval.
No prime distribution or exponential-sum estimate is used. -/
theorem volume_majorArcs_unit_le {Q N : ℕ} (hN : 2 ≤ N) :
    volume (majorArcs Q N ∩ Set.Icc (0 : ℝ) 1) ≤
      ENNReal.ofReal (4 * (Q : ℝ) / N) := by
  calc
    _ ≤ volume (⋃ q ∈ Finset.Icc 1 Q,
        ⋃ a ∈ Finset.range (q + 1), rationalWindow N q a) :=
      measure_mono (majorArcs_unit_subset hN)
    _ ≤ ∑ q ∈ Finset.Icc 1 Q,
        volume (⋃ a ∈ Finset.range (q + 1), rationalWindow N q a) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _q ∈ Finset.Icc 1 Q, ENNReal.ofReal (4 / (N : ℝ)) := by
      apply Finset.sum_le_sum
      intro q hq
      exact volume_windows_fixed_den_le N q (Finset.mem_Icc.mp hq).1
    _ = ENNReal.ofReal (4 * (Q : ℝ) / N) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
      congr 1
      simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      ring

/-- If `4Q < N`, the major arcs do not cover the unit interval. -/
theorem exists_unit_minor {Q N : ℕ} (hN : 2 ≤ N) (hQN : 4 * Q < N) :
    ∃ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 ∧ x ∉ majorArcs Q N := by
  by_contra! h
  have hsubset : Set.Icc (0 : ℝ) 1 ⊆ majorArcs Q N := h
  have hvol := volume_majorArcs_unit_le (Q := Q) hN
  rw [Set.inter_eq_right.mpr hsubset, Real.volume_Icc] at hvol
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hqn : 4 * (Q : ℝ) < N := by exact_mod_cast hQN
  norm_num at hvol
  exact (not_lt_of_ge hvol) ((div_lt_one hn).mpr hqn)

end Problem337.MinorArc

end

end OAI
