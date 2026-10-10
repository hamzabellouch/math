import OAI.NumberTheory.EgyptianFractions.MarkedEndgame
import OAI.NumberTheory.EgyptianFractions.MarkedGroupingUnits
import OAI.NumberTheory.EgyptianFractions.Distinctize

namespace OAI
noncomputable section

open scoped BigOperators

namespace Problem337

/-- The list interface produced by grouping can be cleaned up at fixed length. -/
theorem marked_distinct_tail_of_list (l : List ℕ) {x : ℚ}
    (hx : 0 < x) (hxone : x < 1) (hl : ∀ d ∈ l, 0 < d)
    (hsum : (l.map (fun d : ℕ => (1 : ℚ) / (d : ℚ))).sum = x) :
    ∃ n : Fin l.length → ℕ, IsEgyptianExpansion x n := by
  apply Distinctize.distinctize hx hxone l.get
  · intro i
    exact hl _ (List.get_mem l i)
  · calc
      (∑ i, (1 : ℚ) / (l.get i : ℚ)) =
          (List.ofFn (fun i => (1 : ℚ) / (l.get i : ℚ))).sum := List.sum_ofFn.symm
      _ = (l.map (fun d : ℕ => (1 : ℚ) / (d : ℚ))).sum := by
        change (List.ofFn ((fun d : ℕ => (1 : ℚ) / (d : ℚ)) ∘ l.get)).sum = _
        rw [← List.map_ofFn, List.ofFn_get]
      _ = x := hsum

/-- The qualitative assembly step of the quantitative marked construction.
Only the prefix and the rational-divisor supply remain as inputs. -/
theorem marked_expansion_from_rational_supply
    (m q K R : ℕ) (p : Finset ℕ)
    (hm : 2 ≤ m) (hq : 0 < q) (hK : 0 < K)
    (hR : R < 2 * m) (hRKq : R * K ≤ q)
    (hdensity : HasMarkedDivisorDensity m q)
    (hsupply : HasRationalDivisorSupply m K 16)
    (hp : ∀ d ∈ p, 1 ≤ d) (hmarker : m ∈ p)
    (hsum : (∑ d ∈ p, (1 : ℚ) / (d : ℚ)) + (R : ℚ) / (q : ℚ) = 1)
    (hsmall : ∀ d ∈ p, (R : ℚ) / (q : ℚ) < 1 / (d : ℚ)) :
    ∃ t k : ℕ, ∃ n : Fin k → ℕ,
      k = p.card + t ∧ IsOneExpansion n ∧ (∃ i, n i = m) ∧
      (t : ℝ) ≤ 16 * ((Real.log (K : ℝ) + Real.log (2 * (m : ℝ))) /
        (2 * Real.log (m : ℝ)) + 2) := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos (by linarith)
  by_cases hRzero : R = 0
  · subst R
    obtain ⟨n, hn, hnm⟩ := marked_expansion_of_small_tail p ∅ m hp
      (by simp) hmarker (by simpa using hsum) (by simpa using hsmall)
    refine ⟨0, p.card + 0, n, rfl, hn, hnm, ?_⟩
    have hlogK : 0 ≤ Real.log (K : ℝ) := Real.log_nonneg (by exact_mod_cast hK)
    have hlog2m : 0 ≤ Real.log (2 * (m : ℝ)) := Real.log_nonneg (by linarith)
    norm_num only [Nat.cast_zero]
    positivity
  have hRpos : 0 < R := by omega
  obtain ⟨l, hlen, hlpos, hlsum⟩ :=
    marked_grouping_units_from_list_supply m q K 16 (R * K) hm hq hK hRKq hdensity hsupply
  have hcancel : ((R * K : ℕ) : ℚ) / ((q : ℚ) * (K : ℚ)) = (R : ℚ) / (q : ℚ) := by
    have hKQ : (K : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
  rw [hcancel] at hlsum
  have hx : (0 : ℚ) < (R : ℚ) / (q : ℚ) := by positivity
  have hxone : (R : ℚ) / (q : ℚ) < 1 := by
    have hmQ : (1 : ℚ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    have hfrac : (1 : ℚ) / (m : ℚ) ≤ 1 := by
      exact (div_le_one (by positivity : (0 : ℚ) < m)).2 hmQ
    exact (hsmall m hmarker).trans_le hfrac
  obtain ⟨tail, htail⟩ := marked_distinct_tail_of_list l hx hxone hlpos hlsum
  obtain ⟨n, hn, hnm⟩ := marked_expansion_of_egyptian_tail p m tail hp hmarker htail hsum hsmall
  refine ⟨l.length, p.card + l.length, n, rfl, hn, hnm, ?_⟩
  have hlogRK : Real.log ((R * K : ℕ) : ℝ) ≤
      Real.log (K : ℝ) + Real.log (2 * (m : ℝ)) := by
    rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
    have hRR : (R : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast hR.le
    have hlogR := Real.log_le_log (by positivity : (0 : ℝ) < R) hRR
    linarith
  have hfrac := div_le_div_of_nonneg_right hlogRK (show 0 ≤ 2 * Real.log (m : ℝ) by positivity)
  norm_num at hlen
  simp only [Nat.cast_mul] at hfrac
  linarith

end Problem337

end

end OAI
