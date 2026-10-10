import OAI.NumberTheory.EgyptianFractions.Defs
import OAI.NumberTheory.EgyptianFractions.GreedyPreparation
import OAI.NumberTheory.EgyptianFractions.GreedyBudget
import OAI.NumberTheory.EgyptianFractions.DensityParameters
import OAI.NumberTheory.EgyptianFractions.DenseExpansion
import OAI.NumberTheory.EgyptianFractions.CleanupApplications

namespace OAI
noncomputable section

namespace Problem337

/-- The exact dense-family input required by the elementary main upper reduction.
No distinctness is asked of the supplied lists. -/
def DenseEgyptianFamily (DM L S : ℝ) (C : ℕ) : Prop :=
  ∃ (M : ℕ) (G : Finset ℕ),
    Real.exp S < (M : ℝ) ∧ (M : ℝ) ≤ Real.exp (DM * S) ∧
    ((Finset.Icc 1 ⌊Real.exp ((DM + 2) * S)⌋₊ \ G).card : ℝ) ≤
      Real.exp ((DM + 2) * S) / 8 ∧
    ∀ u ∈ G, ∃ ds : List ℕ,
      (∀ d ∈ ds, 2 ≤ d) ∧ (ds.length : ℝ) ≤ L * Real.log S ∧
      (ds.map (fun d : ℕ => (1 : ℚ) / (d : ℚ))).sum =
        (u : ℚ) / ((M * C : ℕ) : ℚ)

/-- A positive unit-fraction list below one controls the actual minimum length. -/
theorem egyptianLength_le_list_length {a b : ℕ} (hab : a < b)
    (l : List ℕ) (hden : ∀ d ∈ l, 2 ≤ d)
    (hsum : (l.map (fun d : ℕ => (1 : ℚ) / (d : ℚ))).sum =
      (a : ℚ) / (b : ℚ)) : egyptianLength a b ≤ l.length := by
  have hb : (0 : ℚ) < b := by exact_mod_cast (show 0 < b by omega)
  obtain ⟨n, hn⟩ := egyptian_expansion_of_list ((a : ℚ) / (b : ℚ))
    ((div_lt_one hb).mpr (by exact_mod_cast hab)) l
    (fun d hd => le_trans (by decide) (hden d hd)) hsum
  exact Nat.sInf_le (show l.length ∈ egyptianLengths a b from ⟨n, hn⟩)

/-- For one fixed large denominator, the dense input and greedy preparation give
an explicit uniform length coefficient. -/
theorem egyptianLength_upper_of_dense_at
    (DM L : ℝ) (hDM : 1 < DM) (hL : 0 < L)
    (b N : ℕ) (hb : 2 ≤ b) (hS : Real.exp 1 ≤ Real.log (b : ℝ))
    (hbudget : ((N + 1 : ℕ) : ℝ) ≤
      (2 / Real.log 2 + 2) * Real.log (Real.log (b : ℝ)))
    (hcap : Real.exp (4 * (DM + 2) * Real.log (b : ℝ)) *
      (1 / 2 : ℝ) ^ (2 ^ N) ≤ 1)
    (hdensity : ∀ C : ℕ,
      Real.exp (4 * (DM + 2) * Real.log (b : ℝ)) ≤ (C : ℝ) →
      (C : ℝ) ≤ Real.exp (2 * (4 * (DM + 2)) * Real.log (b : ℝ)) →
      DenseEgyptianFamily DM L (Real.log (b : ℝ)) C) :
    ∀ a : ℕ, 1 ≤ a → a < b →
      (egyptianLength a b : ℝ) ≤
        (2 / Real.log 2 + 2 + 2 * L + 2) * Real.log (Real.log (b : ℝ)) := by
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hloglog : 1 ≤ Real.log (Real.log (b : ℝ)) := by
    have := Real.log_le_log (Real.exp_pos 1) hS
    simpa using this
  have hS1 : 1 ≤ Real.log (b : ℝ) := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hrange := dense_preparation_ranges DM (Real.log (b : ℝ)) hDM hS1
  have hbT : (b : ℝ) < Real.exp (4 * (DM + 2) * Real.log (b : ℝ)) := by
    simpa [Real.exp_log hbpos] using hrange.2.1
  intro a ha hab
  obtain ⟨l, A, C, hlen, hden, hAa, hC, hsum, halt⟩ :=
    greedy_preparation a b N (Real.exp (4 * (DM + 2) * Real.log (b : ℝ)))
      ha hab hbT hcap
  simp only [List.bind_eq_flatMap, List.pure_def, ← List.map_eq_flatMap,
    List.map_map, Function.comp_def] at hsum
  rcases halt with hA0 | ⟨hA, hClow, hCup⟩
  · have hsum' : (l.map (fun d : ℕ => (1 : ℚ) / (d : ℚ))).sum =
        (a : ℚ) / (b : ℚ) := by simpa only [hA0, Nat.cast_zero, zero_div, add_zero] using hsum
    have hmin := egyptianLength_le_list_length hab l hden hsum'
    have hminR : (egyptianLength a b : ℝ) ≤ l.length := by exact_mod_cast hmin
    have hlenR : (l.length : ℝ) ≤ (N + 1 : ℕ) := by exact_mod_cast hlen
    nlinarith
  · have hCup' : (C : ℝ) ≤
        Real.exp (2 * (4 * (DM + 2)) * Real.log (b : ℝ)) := by
      rw [hrange.2.2.2.1] at hCup
      exact hCup.le
    obtain ⟨M, G, hMlow, hMup, hholes, hG⟩ := hdensity C hClow hCup'
    have hM : 0 < M := by
      have : (0 : ℝ) < M := (Real.exp_pos _).trans hMlow
      exact_mod_cast this
    have hAM : ((A * M : ℕ) : ℝ) ≤ Real.exp ((DM + 2) * Real.log (b : ℝ)) := by
      push_cast
      apply hrange.2.2.2.2 A M (by positivity) ?_ (by positivity) hMup
      rw [Real.exp_log hbpos]
      exact_mod_cast (show A ≤ b by omega)
    let K : ℕ := ⌈L * Real.log (Real.log (b : ℝ))⌉₊
    have hGK : ∀ u ∈ G, ∃ ds : List ℕ,
        (∀ d ∈ ds, 2 ≤ d) ∧ ds.length ≤ K ∧
        (ds.map (fun d : ℕ => (1 : ℚ) / (d : ℚ))).sum =
          (u : ℚ) / ((M * C : ℕ) : ℚ) := by
      intro u hu
      obtain ⟨ds, hd, hl, hs⟩ := hG u hu
      refine ⟨ds, hd, ?_, hs⟩
      have hh : (ds.length : ℝ) ≤ K := hl.trans (Nat.le_ceil _)
      exact_mod_cast hh
    obtain ⟨tail, htail, htaillen, htailsum⟩ := dense_expansion_of_lists
      (Real.exp ((DM + 2) * Real.log (b : ℝ))) A C M K G hA hC hM
      hrange.2.2.1 hAM hholes hGK
    have hall : ∀ d ∈ l ++ tail, 2 ≤ d := by
      intro d hd
      exact (List.mem_append.mp hd).elim (hden d) (htail d)
    have hfullsum : ((l ++ tail).map (fun d : ℕ => (1 : ℚ) / (d : ℚ))).sum =
        (a : ℚ) / (b : ℚ) := by
      rw [List.map_append, List.sum_append, htailsum]
      exact hsum
    have hmin := egyptianLength_le_list_length hab (l ++ tail) hall hfullsum
    have hminR : (egyptianLength a b : ℝ) ≤ (l.length : ℝ) + tail.length := by
      exact_mod_cast (show egyptianLength a b ≤ l.length + tail.length by simpa using hmin)
    have hlenR : (l.length : ℝ) ≤ (N + 1 : ℕ) := by exact_mod_cast hlen
    have htailR : (tail.length : ℝ) ≤ 2 * (K : ℝ) := by exact_mod_cast htaillen
    have hK : (K : ℝ) < L * Real.log (Real.log (b : ℝ)) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    nlinarith

/-- Complete elementary reduction of the uniform upper bound to the dense-family
proposition. All other inputs (greedy stopping, splitting, and distinctification)
are proved in the imported modules. -/
theorem main_upper_of_dense_family
    (DM L S0 : ℝ) (hDM : 1 < DM) (hL : 0 < L)
    (hdensity : ∀ S : ℝ, S0 ≤ S → ∀ C : ℕ,
      Real.exp (4 * (DM + 2) * S) ≤ (C : ℝ) →
      (C : ℝ) ≤ Real.exp (2 * (4 * (DM + 2)) * S) →
      DenseEgyptianFamily DM L S C) :
    ∃ c2 : ℝ, 0 < c2 ∧ ∃ b0 : ℕ, ∀ b : ℕ, b0 ≤ b →
      (maxEgyptianLength b : ℝ) ≤ c2 * Real.log (Real.log (b : ℝ)) := by
  let c2 : ℝ := 2 / Real.log 2 + 2 + 2 * L + 2
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc2 : 0 < c2 := by dsimp [c2]; positivity
  obtain ⟨b1, hbudget⟩ := eventually_logarithmic_greedy_budget (4 * (DM + 2))
  obtain ⟨b2, hparams⟩ := eventually_dense_preparation_ranges DM (max S0 (Real.exp 1)) hDM
  refine ⟨c2, hc2, max b1 b2, fun b hb => ?_⟩
  obtain ⟨N, hN, hcap⟩ := hbudget b (le_trans (le_max_left _ _) hb)
  obtain ⟨hb2, hS, _, _, _⟩ := hparams b (le_trans (le_max_right _ _) hb)
  have hS0 : S0 ≤ Real.log (b : ℝ) := (le_max_left _ _).trans hS
  have hSexp : Real.exp 1 ≤ Real.log (b : ℝ) := (le_max_right _ _).trans hS
  have hupper : ∀ a : ℕ, 1 ≤ a → a < b →
      (egyptianLength a b : ℝ) ≤ c2 * Real.log (Real.log (b : ℝ)) :=
    egyptianLength_upper_of_dense_at DM L hDM hL b N hb2 hSexp hN hcap
      (hdensity (Real.log (b : ℝ)) hS0)
  have hloglog : 1 ≤ Real.log (Real.log (b : ℝ)) := by
    have := Real.log_le_log (Real.exp_pos 1) hSexp
    simpa using this
  have hnonneg : 0 ≤ c2 * Real.log (Real.log (b : ℝ)) := by positivity
  have hmax : maxEgyptianLength b ≤ ⌊c2 * Real.log (Real.log (b : ℝ))⌋₊ := by
    unfold maxEgyptianLength
    apply Finset.sup_le
    intro a ha
    by_cases hapos : 1 ≤ a
    · rw [ite_eq_left hapos]
      exact Nat.le_floor (hupper a hapos (Finset.mem_range.mp ha))
    · simp [hapos]
  exact (show (maxEgyptianLength b : ℝ) ≤
    (⌊c2 * Real.log (Real.log (b : ℝ))⌋₊ : ℝ) by exact_mod_cast hmax).trans
      (Nat.floor_le hnonneg)

end Problem337

end

end OAI
