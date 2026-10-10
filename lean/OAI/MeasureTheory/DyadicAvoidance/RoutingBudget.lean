import OAI.MeasureTheory.DyadicAvoidance.WindowBudgets
import OAI.MeasureTheory.DyadicAvoidance.MonotoneRepresentatives

namespace OAI

noncomputable section

namespace Problem310.RoutingBudget

/-- Transfer a real finite-union estimate to the extended-nonnegative probability scale. -/
lemma ennreal_card_mul_pow_lt {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q)
    (N k : ℕ) (h : (N : ℝ) * q ^ k < p) :
    (N : ENNReal) * (ENNReal.ofReal q) ^ k < ENNReal.ofReal p := by
  have he := (ENNReal.ofReal_lt_ofReal_iff hp).2 h
  simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg N), ENNReal.ofReal_natCast,
    ENNReal.ofReal_pow hq] using he

/-- Choose parameters in the router convention: `M` is the number of nondefault
children, so there are `M + 1` children altogether. The last estimate is ready for
an `ENNReal` finite union bound over the monotone-key representatives. -/
theorem exists_nondefault_parameters (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∃ M d R : ℕ, 1 ≤ M ∧ 1 ≤ d ∧ 1 ≤ R ∧
      10 ≤ p * (M : ℝ) / 2 ∧
      (1 - ((2 : ℝ)⁻¹) ^ M) ^ d < p ∧
      ∀ r : ℕ, R ≤ r → ∀ N : ℕ,
        N ≤ 1 + M * r * 2 ^ (2 * r + 2) →
        (N : ENNReal) * (ENNReal.ofReal (1 - p / 2)) ^ (M * r) <
          ENNReal.ofReal p := by
  obtain ⟨T, d, hT, hd, hmargin, hdepth⟩ :=
    WindowBudget.exists_tree_parameters p hp
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : T ≠ 0)
  obtain ⟨R, hR, hsmall⟩ :=
    WindowBudget.exists_probability_threshold p hp hp1 (M + 1) hT hmargin
  have hM : 1 ≤ M := by omega
  have hmargin' : 10 ≤ p * (M : ℝ) / 2 := by
    simpa only [Nat.cast_succ, add_sub_cancel_right] using hmargin
  simp only [Nat.add_sub_cancel] at hdepth hsmall
  refine ⟨M, d, R, hM, hd, hR, hmargin', hdepth, ?_⟩
  intro r hr N hN
  have hrpos : 1 ≤ r := hR.trans hr
  have hcard := ScaleDiscretization.representative_card_budget
    (M + 1) r (2 ^ (2 * r + 2)) (by omega) hrpos
  simp only [Nat.add_sub_cancel] at hcard
  have hNbig : N ≤ 20 * (M + 1) * r * (1 + 2 ^ (2 * r + 2)) :=
    hN.trans hcard
  have hNreal : (N : ℝ) ≤ 20 * ((M + 1 : ℕ) : ℝ) * (r : ℝ) *
      (1 + (2 : ℝ) ^ (2 * r + 2)) := by
    exact_mod_cast hNbig
  apply ennreal_card_mul_pow_lt hp (by linarith) N (M * r)
  exact (mul_le_mul_of_nonneg_right hNreal (pow_nonneg (by linarith) _)).trans_lt
    (hsmall r hr)

/-- The real survival estimate has exactly the expected truncated-subtraction
form for the product probability measure. -/
lemma ennreal_survival_lt {p : ℝ} (hp : 0 < p) (M d : ℕ)
    (h : (1 - ((2 : ℝ)⁻¹) ^ M) ^ d < p) :
    (1 - ((2 : ENNReal)⁻¹) ^ M) ^ d < ENNReal.ofReal p := by
  have hbase0 : 0 ≤ 1 - ((2 : ℝ)⁻¹) ^ M := by
    have hpow : ((2 : ℝ)⁻¹) ^ M ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith
  have hbase : ENNReal.ofReal (1 - ((2 : ℝ)⁻¹) ^ M) =
      1 - ((2 : ENNReal)⁻¹) ^ M := by
    rw [ENNReal.ofReal_sub 1 (by positivity), ENNReal.ofReal_one,
      ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  have he := (ENNReal.ofReal_lt_ofReal_iff hp).2 h
  rwa [ENNReal.ofReal_pow hbase0, hbase] at he

end Problem310.RoutingBudget

end

end OAI
