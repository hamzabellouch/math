import OAI.NumberTheory.EgyptianFractions.MarkedEndgame
import OAI.NumberTheory.EgyptianFractions.MarkedBudget

namespace OAI
noncomputable section

open Filter

namespace Problem337

/-- A final reduction of the quantitative marked target to the explicit
construction bounds, before asymptotic error absorption. -/
theorem quantitative_marked_length_of_explicit_budget (K : ℕ → ℝ)
    (hKpositive : ∀ᶠ m : ℕ in atTop, 1 ≤ K m)
    (hK : ∀ δ : ℝ, 0 < δ → ∀ᶠ m : ℕ in atTop,
      Real.log (K m) ≤ (32 / Real.log 2 + δ) * Real.log (m : ℝ) *
        Real.log (Real.log (m : ℝ)))
    (hconstruct : ∀ᶠ m : ℕ in atTop,
      ∃ j t k : ℕ, ∃ n : Fin k → ℕ,
        IsOneExpansion n ∧ (∃ i, n i = m) ∧ k ≤ 1 + j + t ∧
        (j : ℝ) ≤ 3 + (Real.log (Real.log (2 * (m : ℝ) * K m)) -
          Real.log (Real.log 2)) / Real.log 2 ∧
        (t : ℝ) ≤ 16 * ((Real.log (K m) + Real.log (2 * (m : ℝ))) /
          (2 * Real.log (m : ℝ)) + 2)) :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, 2 ≤ M ∧
      ∀ m : ℕ, M ≤ m → ∃ k : ℕ, ∃ n : Fin k → ℕ,
        IsOneExpansion n ∧ (∃ i, n i = m) ∧
        (k : ℝ) ≤ (257 / Real.log 2 + ε) * Real.log (Real.log (m : ℝ)) := by
  intro ε hε
  let J : ℕ → ℝ := fun m => 3 + (Real.log (Real.log (2 * (m : ℝ) * K m)) -
    Real.log (Real.log 2)) / Real.log 2
  let G : ℕ → ℝ := fun m => (Real.log (K m) + Real.log (2 * (m : ℝ))) /
    (2 * Real.log (m : ℝ)) + 2
  have hJ := marked_prefix_budget K J hKpositive (hK 1 zero_lt_one)
    (Eventually.of_forall (fun m => le_rfl)) (ε / 34) (by positivity)
  have hG := marked_group_budget K G hK
    (Eventually.of_forall (fun m => le_rfl)) (ε / 34) (by positivity)
  have hloglog : Tendsto (fun m : ℕ => Real.log (Real.log (m : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hlarge : ∀ᶠ m : ℕ in atTop, 2 / ε ≤ Real.log (Real.log (m : ℝ)) :=
    hloglog.eventually (eventually_ge_atTop (2 / ε))
  have hevent : ∀ᶠ m : ℕ in atTop, ∃ k : ℕ, ∃ n : Fin k → ℕ,
      IsOneExpansion n ∧ (∃ i, n i = m) ∧
      (k : ℝ) ≤ (257 / Real.log 2 + ε) * Real.log (Real.log (m : ℝ)) := by
    filter_upwards [hconstruct, hJ, hG, hlarge] with m hm hJ hG hlarge
    obtain ⟨j, t, k, n, hn, hmarker, hk, hj, ht⟩ := hm
    refine ⟨k, n, hn, hmarker, ?_⟩
    have hj' : (j : ℝ) ≤ (1 / Real.log 2 + ε / 34) * Real.log (Real.log (m : ℝ)) :=
      hj.trans hJ
    have ht' : (t : ℝ) ≤ 16 * ((16 / Real.log 2 + ε / 34) * Real.log (Real.log (m : ℝ))) :=
      ht.trans (mul_le_mul_of_nonneg_left hG (by norm_num))
    have hkR : (k : ℝ) ≤ 1 + (j : ℝ) + (t : ℝ) := by exact_mod_cast hk
    have hlarge' : 2 ≤ Real.log (Real.log (m : ℝ)) * ε :=
      (div_le_iff₀ hε).1 hlarge
    have hcoef : (1 : ℝ) / Real.log 2 + 16 * (16 / Real.log 2) = 257 / Real.log 2 := by ring
    nlinarith
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  refine ⟨max 2 N, le_max_left _ _, ?_⟩
  intro m hm
  exact hN m ((le_max_right _ _).trans hm)

end Problem337

end

end OAI
