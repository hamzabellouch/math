import OAI.NumberTheory.EgyptianFractions.Defs

namespace OAI
noncomputable section
open scoped BigOperators
open Filter

namespace Problem337

lemma denominator_ncard_le (k : ℕ) (hfin : (OneExpansions k).Finite) :
    (D k).ncard ≤ k * F k := by
  let S : Set ((Fin k → ℕ) × Fin k) := OneExpansions k ×ˢ Set.univ
  let f : ((Fin k → ℕ) × Fin k) → ℕ := fun p => p.1 p.2
  have hS : S.Finite := hfin.prod Set.finite_univ
  have hsub : D k ⊆ f '' S := by
    rintro m ⟨hm, n, hn, i, rfl⟩
    exact ⟨⟨n, i⟩, ⟨hn, Set.mem_univ i⟩, rfl⟩
  calc
    (D k).ncard ≤ (f '' S).ncard := Set.ncard_le_ncard hsub (hS.image f)
    _ ≤ S.ncard := Set.ncard_image_le hS
    _ = k * F k := by simp [S, Set.ncard_prod, F, Nat.mul_comm]

lemma missing_le_count (k : ℕ) (hfin : (OneExpansions k).Finite)
    (hDfin : (D k).Finite)
    (hcover : ∀ m, 2 ≤ m → m < v k → m ∈ D k) :
    v k ≤ k * F k + 2 := by
  have hsub : Set.Ico 2 (v k) ⊆ D k := fun m hm => hcover m hm.1 hm.2
  have hc := Set.ncard_le_ncard hsub hDfin
  have hb := denominator_ncard_le k hfin
  rw [Set.ncard_Ico_nat] at hc
  omega

/-- Counting available exact markers forces many expansions. The explicit threshold is
irrelevant asymptotically, but keeps this bridge entirely elementary. -/
lemma loglog_count_lower_of_missing (k f w : ℕ) (hk : 6000000 ≤ k)
    (hlarge : Real.exp (Real.exp ((k : ℝ) / 600)) ≤ (w : ℝ))
    (hcount : w ≤ k * f + 2) :
    (k : ℝ) / 1200 ≤ Real.log (Real.log (f : ℝ)) := by
  have hkR : (6000000 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
  have hx0 : 0 ≤ (k : ℝ) / 1200 := by positivity
  have hquad := Real.pow_div_factorial_le_exp ((k : ℝ) / 1200) hx0 2
  norm_num at hquad
  have hexp : (k : ℝ) + 2 ≤ Real.exp ((k : ℝ) / 1200) := by
    have hmul : 0 ≤ ((k : ℝ) - 6000000) * (k : ℝ) :=
      mul_nonneg (by linarith) hk0.le
    nlinarith
  have htwo : 2 ≤ Real.exp ((k : ℝ) / 1200) := by linarith
  have hdouble : Real.exp ((k : ℝ) / 1200) + Real.exp ((k : ℝ) / 1200) ≤
      Real.exp ((k : ℝ) / 600) := by
    rw [show (k : ℝ) / 600 = (k : ℝ) / 1200 + (k : ℝ) / 1200 by ring,
      Real.exp_add]
    nlinarith
  let E : ℝ := Real.exp (Real.exp ((k : ℝ) / 1200))
  have hEpos : 0 < E := Real.exp_pos _
  have hE : (k : ℝ) + 2 ≤ E := by
    have hle := Real.add_one_le_exp (Real.exp ((k : ℝ) / 1200))
    dsimp [E]
    linarith
  have hEsq : E * E ≤ Real.exp (Real.exp ((k : ℝ) / 600)) := by
    dsimp [E]
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr hdouble
  have hcountR : (w : ℝ) ≤ (k : ℝ) * (f : ℝ) + 2 := by exact_mod_cast hcount
  have hf : E ≤ (f : ℝ) := by
    by_contra h
    have hlt : (f : ℝ) < E := lt_of_not_ge h
    have hmul := mul_lt_mul_of_pos_left hlt hk0
    have hmul' := mul_le_mul_of_nonneg_right hE hEpos.le
    nlinarith
  have hfpos : 0 < (f : ℝ) := lt_of_lt_of_le hEpos hf
  have hlog : Real.exp ((k : ℝ) / 1200) ≤ Real.log (f : ℝ) :=
    (Real.le_log_iff_exp_le hfpos).2 hf
  exact (Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos _) hlog)).2 hlog

theorem counting_order_of_missing_lower
    (hfin : ∀ k, (OneExpansions k).Finite)
    (hDfin : ∀ k, (D k).Finite)
    (hcover : ∀ k m, 2 ≤ m → m < v k → m ∈ D k)
    (hupper : ∀ k, 2 ≤ k → Real.log (Real.log (F k : ℝ)) ≤ 3 * (k : ℝ))
    (hlower : ∃ k0 : ℕ, ∀ k, k0 ≤ k →
      Real.exp (Real.exp ((k : ℝ) / 600)) ≤ (v k : ℝ)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ k0 : ℕ,
      ∀ k : ℕ, k0 ≤ k →
        c * (k : ℝ) ≤ Real.log (Real.log (F k : ℝ)) ∧
        Real.log (Real.log (F k : ℝ)) ≤ C * (k : ℝ) := by
  obtain ⟨K, hK⟩ := hlower
  refine ⟨1 / 1200, 3, by norm_num, by norm_num, max 6000000 K, ?_⟩
  intro k hk
  have hk1 : 6000000 ≤ k := le_trans (le_max_left _ _) hk
  have hk2 : K ≤ k := le_trans (le_max_right _ _) hk
  constructor
  · convert loglog_count_lower_of_missing k (F k) (v k) hk1 (hK k hk2)
      (missing_le_count k (hfin k) (hDfin k) (hcover k)) using 1
    ring
  · exact hupper k (by omega)

end Problem337

end

end OAI
