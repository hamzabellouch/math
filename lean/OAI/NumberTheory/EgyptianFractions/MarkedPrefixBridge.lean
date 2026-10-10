import OAI.NumberTheory.EgyptianFractions.MarkedReduction
import OAI.NumberTheory.EgyptianFractions.MarkedGreedyDensity
import OAI.NumberTheory.EgyptianFractions.MarkedGreedyLength

namespace OAI
noncomputable section

open scoped BigOperators

namespace Problem337

/-- Translate the finite marked greedy list into the exact finite-set contract
consumed by the quantitative endgame. -/
theorem quantitative_marked_prefix_of_short_list
    (m K R q : ℕ) (L : List ℕ) (hm : 4 ≤ m) (hK : m ≤ K)
    (htrace : MarkedGreedySteps m (m - 1) m L R q)
    (hpair : L.Pairwise (· < ·)) (hlist : ∀ d ∈ L, 2 ≤ d ∧ d ≠ m)
    (hq : 0 < q) (hR : R < 2 * m)
    (hsum : (1 : ℚ) = 1 / (m : ℚ) +
      (L.map (fun d : ℕ => (1 : ℚ) / (d : ℚ))).sum + (R : ℚ) / (q : ℚ))
    (hstop : R = 0 ∨ 2 * m * K ≤ q)
    (hmarker : m * R < q) (hfinal : ∀ d ∈ L, d * R < q)
    (hlen : (L.length : ℝ) ≤ 3 +
      (Real.log (Real.log (2 * (m : ℝ) * (K : ℝ))) - Real.log (Real.log 2)) /
        Real.log 2) :
    HasQuantitativeMarkedPrefix m K := by
  classical
  have hnodup : L.Nodup := hpair.nodup
  have hRKq : R * K ≤ q := by
    rcases hstop with hzero | hlarge
    · simp [hzero]
    · nlinarith
  have hdense : HasMarkedDivisorDensity m q := htrace.divisorDense (by omega)
  refine ⟨L.toFinset, q, R, hq, hR, hRKq, hdense, ?_, ?_, ?_, ?_, ?_⟩
  · intro d hd
    have := (hlist d (List.mem_toFinset.1 hd)).1
    omega
  · intro hmL
    exact (hlist m (List.mem_toFinset.1 hmL)).2 rfl
  · rw [List.sum_toFinset _ hnodup]
    exact hsum.symm
  · intro d hd
    have hdpos : 0 < d := by
      rcases Finset.mem_insert.1 hd with rfl | hd
      · omega
      · have := (hlist d (List.mem_toFinset.1 hd)).1
        omega
    have hdR : d * R < q := by
      rcases Finset.mem_insert.1 hd with rfl | hd
      · exact hmarker
      · exact hfinal d (List.mem_toFinset.1 hd)
    apply (div_lt_div_iff₀ (show (0 : ℚ) < q by positivity)
      (show (0 : ℚ) < d by positivity)).2
    have hdR' : (d : ℚ) * (R : ℚ) < q := by exact_mod_cast hdR
    nlinarith
  · rw [List.toFinset_card_of_nodup hnodup]
    exact hlen

/-- The complete marked greedy construction discharges the prefix prerequisite
for every multiplier at least as large as the marker. -/
theorem hasQuantitativeMarkedPrefix_of_le (m K : ℕ) (hm : 4 ≤ m) (hK : m ≤ K) :
    HasQuantitativeMarkedPrefix m K := by
  have hT : 2 * m ^ 2 ≤ 2 * m * K := by nlinarith
  obtain ⟨L, R, q, htrace, hpair, hlist, hqeq, hq, hR, hsum,
    hqbound, hstop, hmarker, hfinal, hlen⟩ :=
      exists_marked_greedy_prefix_short m (2 * m * K) hm hT
  apply quantitative_marked_prefix_of_short_list m K R q L hm hK htrace hpair hlist
    hq hR hsum hstop hmarker hfinal
  have hTreal : (1 : ℝ) < ((2 * m * K : ℕ) : ℝ) := by
    exact_mod_cast (show 1 < 2 * m * K by nlinarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [Real.log_div (ne_of_gt (Real.log_pos hTreal)) (ne_of_gt hlog2)] at hlen
  push_cast at hlen
  exact hlen.le

end Problem337

end

end OAI
