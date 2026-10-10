import OAI.Probability.ThorpRouting.RegularTrace

namespace OAI

noncomputable section
open scoped BigOperators

namespace ThorpNine.Harmonic.Thorp.LowPlanes
open Casimir Specht UnitaryFinite

attribute [local instance] hsNorm hsInner hsFinite

def weightedMoment (d r : ℕ) (μ : Shapes (2 ^ d)) : ℝ :=
  (Module.finrank ℂ (hilbertSpace μ.1) : ℝ) *
    (LinearMap.trace ℂ (hilbertSpace μ.1)
      ((star (Q d μ) * Q d μ) ^ r).toLinearMap).re

lemma trace_mul_power_comm {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (A B : V →L[ℂ] V) (r : ℕ) :
    LinearMap.trace ℂ V ((A * B) ^ r).toLinearMap =
      LinearMap.trace ℂ V ((B * A) ^ r).toLinearMap := by
  simp only [ContinuousLinearMap.toLinearMap_pow, ContinuousLinearMap.toLinearMap_mul]
  cases r with
  | zero => rfl
  | succ r =>
    rw [pow_succ, ← mul_assoc, mul_pow_mul, LinearMap.trace_mul_comm,
      ← mul_assoc, ← pow_succ']

theorem uniform_weighted_moment :
    ∃ r : ℕ, Even r ∧ 2 ≤ r ∧ ∀ d (μ : Shapes (2 ^ d)),
      weightedMoment d r μ ≤ 1 := by
  obtain ⟨b, hb, hdim⟩ := HarmonicBounds.dimension_contraction
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / b)
  have hbm : 1 < b * (m : ℝ) := by
    have h := (div_lt_iff₀ hb).mp hm
    nlinarith
  have hmpos : 0 < m := by
    by_contra h
    have hz : m = 0 := by omega
    simp [hz] at hbm
    linarith
  refine ⟨2 * m, even_two_mul m, by omega, ?_⟩
  intro d μ
  by_cases hz : μ.1.card - μ.1.rowLen 0 = 0
  · have h := full_row_trace d (2 * m) μ hz
    rw [absoluteTrace_even] at h
    exact h.le
  · have hk : 0 < μ.1.card - μ.1.rowLen 0 := by omega
    let D : ℝ := Module.finrank ℂ (hilbertSpace μ.1)
    have hD : 0 < D := by
      dsimp [D]
      rw [finrank_hilbertSpace]
      exact_mod_cast dimension_pos μ.1
    have hlog : 0 ≤ Real.log D := Real.log_nonneg (by
      dsimp [D]
      rw [finrank_hilbertSpace]
      exact_mod_cast dimension_pos μ.1)
    have hc := hdim d μ.1 (cardLabels d μ) hk
    rw [← finrank_hilbertSpace] at hc
    change ‖K d μ.1 (cardLabels d μ)‖ ≤ Real.exp (-b * Real.log D) at hc
    have hp := pow_le_pow_left₀ (norm_nonneg _) hc (2 * m)
    change D * _ ≤ 1
    rw [Q_square]
    calc
      _ ≤ D * (D * ‖K d μ.1 (cardLabels d μ)‖ ^ (2 * m)) :=
        mul_le_mul_of_nonneg_left
          (trace_power_le_dimension_norm _ _ (by omega)) hD.le
      _ ≤ D * (D * (Real.exp (-b * Real.log D)) ^ (2 * m)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp hD.le) hD.le
      _ = Real.exp ((2 - b * (2 * m : ℕ)) * Real.log D) := by
        nth_rw 1 [← Real.exp_log hD]
        nth_rw 2 [← Real.exp_log hD]
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
        congr 1
        push_cast
        ring
      _ ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
        (by push_cast; nlinarith) hlog)

theorem four_row_fixed_moment :
    ∃ r : ℕ, Even r ∧ 2 ≤ r ∧ ∃ η : ℝ, 0 < η ∧
      ∀ d (μ : Shapes (2 ^ d)),
        (Module.finrank ℂ (hilbertSpace μ.1) : ℝ) *
          (LinearMap.trace ℂ (hilbertSpace μ.1)
            ((Q d μ * star (Q d μ)) ^ r).toLinearMap).re ≤
          (Module.finrank ℂ (hilbertSpace μ.1) : ℝ) ^ (1 - η) := by
  obtain ⟨r, he, hr, h⟩ := uniform_weighted_moment
  refine ⟨r, he, hr, 1, by norm_num, ?_⟩
  intro d μ
  rw [trace_mul_power_comm]
  simpa [weightedMoment] using h d μ

theorem bounded_regular_schatten_moment :
    ∃ P : ℝ, 0 < P ∧ ∀ d : ℕ, 1 ≤ d →
      regularTrace d P ≤ 1 + 1 / 16 := by
  obtain ⟨P, hP, h⟩ := regular_trace_smoothing
  refine ⟨P, by linarith, ?_⟩
  intro d hd
  apply (h d hd).1.trans
  have hn : (2 : ℝ) ≤ 2 ^ d := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hd
  have hp : (2 : ℝ) ^ d > 0 := by positivity
  have hpow : (2 : ℝ) ^ 10 ≤ ((2 : ℝ) ^ d) ^ 10 :=
    pow_le_pow_left₀ (by norm_num) hn 10
  have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2 ^ 10) hpow
  have he : ((2 : ℝ) ^ d) ^ (-10 : ℤ) ≤ 1 / 16 := by
    rw [zpow_neg, zpow_ofNat]
    rw [inv_eq_one_div]
    exact hi.trans (by norm_num)
  linarith

lemma dyadic_negative_power_le (d k : ℕ) (hd : 1 ≤ d) :
    ((2 : ℝ) ^ d) ^ (-(k : ℤ)) ≤ ((2 : ℝ) ^ k)⁻¹ := by
  rw [zpow_neg, zpow_natCast]
  apply inv_anti₀ (by positivity)
  apply pow_le_pow_left₀ (by norm_num)
  simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hd

theorem bounded_regular_moment :
    ∃ p : ℝ, 0 < p ∧ ∀ d : ℕ, 1 ≤ d →
      regularTrace d (2 * p) ≤ 1 + 1 / 16 ∧
      ∀ M : ℕ, p ≤ M → ∀ σ : Equiv.Perm (Card d),
        sweepDistance d M σ ≤ 1 / 8 := by
  obtain ⟨P, hP, h⟩ := regular_trace_smoothing
  refine ⟨P / 2, by linarith, ?_⟩
  intro d hd
  constructor
  · rw [show 2 * (P / 2) = P by ring]
    apply (h d hd).1.trans
    have hi := dyadic_negative_power_le d 10 hd
    norm_num at hi
    rw [zpow_neg, zpow_ofNat]
    linarith
  · intro M hM σ
    have hi := (h d hd).2 (M : ℤ) (by exact_mod_cast (show P ≤ 2 * (M : ℝ) by linarith)) σ
    simp only [Int.toNat_natCast] at hi
    apply hi.trans
    have hp := dyadic_negative_power_le d 5 hd
    norm_num at hp
    rw [zpow_neg, zpow_ofNat]
    linarith

end ThorpNine.Harmonic.Thorp.LowPlanes

end

end OAI
