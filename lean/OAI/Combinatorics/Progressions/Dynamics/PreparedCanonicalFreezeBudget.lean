import OAI.Combinatorics.Progressions.Dynamics.PreparedFreezingEarlyLogBudget
import OAI.Combinatorics.Progressions.Estimates.PreparedFamilyCanonicalGeometry

namespace OAI

section

namespace Erdos3
open scoped BigOperators

noncomputable def preparedCanonicalFreezeLog (p : ℝ) (M m : ℕ) : ℝ :=
  p + M + m + allocatedUniformChartLog (M : ℝ) + 1

theorem exists_preparedCanonicalFreeze_power (s capPower : ℕ) :
    ∃ e : ℕ, 2 ≤ e ∧ ∀ {p : ℝ}, 0 ≤ p → ∀ M m : ℕ,
      (M : ℝ) ≤ (p + 2) ^ capPower → m ≤ s →
      6 * preparedCanonicalFreezeLog p M m + 130 ≤ (p + 2) ^ e := by
  let Q : Polynomial ℕ := Polynomial.X + (Polynomial.X + 2) ^ capPower +
    Polynomial.C s + 20 * ((Polynomial.X + 2) ^ capPower + 1) ^ 3 + 1
  obtain ⟨e, he, hbound⟩ := exists_natPolynomial_fixed_power_budget (6 * Q + 130)
  refine ⟨e, he, ?_⟩
  intro p hp M m hM hm
  have hlog : preparedCanonicalFreezeLog p M m ≤
      p + (p + 2) ^ capPower + s + 20 * ((p + 2) ^ capPower + 1) ^ 3 + 1 := by
    unfold preparedCanonicalFreezeLog allocatedUniformChartLog
    gcongr
  have hpoly : 6 * (p + (p + 2) ^ capPower + s +
      20 * ((p + 2) ^ capPower + 1) ^ 3 + 1) + 130 ≤ (p + 2) ^ e := by
    simpa [Q, Polynomial.eval₂_pow] using hbound p hp
  linarith

theorem preparedCanonicalFreeze_log_bounds {X J : Type} {s D E m M : ℕ}
    (A : PolynomialPatch X s (D + E)) (L : RankPreparationFamily X J m)
    {p gain δ : ℝ} (hp : 0 ≤ p) (hA : relativePatchComplexity A ≤ p)
    (hM : ∀ j, Fintype.card (L j).Coord ≤ M)
    (hgain : Real.exp (-p) ≤ gain)
    (hδ : δ ≤ Real.exp (-(3 * preparedCanonicalFreezeLog p M m + 130))) :
    let q := preparedCanonicalFreezeLog p M m
    0 ≤ q ∧ (D : ℝ) ≤ Real.exp q ∧ (m : ℝ) ≤ Real.exp q ∧
      (A.kernel.lip : ℝ) ≤ Real.exp q ∧
      (∀ j, (Fintype.card (L j).Coord : ℝ) ≤ Real.exp q) ∧
      Real.exp (allocatedUniformChartLog (M : ℝ)) ≤ Real.exp q ∧
      Real.exp (-q) ≤ gain ∧
      (∀ j, (32 * ((D : ℝ) + 1) * ((A.kernel.lip : ℝ) + 1) * ((m : ℝ) + 1) / gain) *
        (Fintype.card (L j).Coord : ℝ) * Real.exp (allocatedUniformChartLog (M : ℝ)) ≤
          Real.exp (6 * q + 35)) ∧
      δ ≤ gain / (128 * ((D : ℝ) + 1) * ((A.kernel.lip : ℝ) + 1)) := by
  intro q
  have hchart0 : 0 ≤ allocatedUniformChartLog (M : ℝ) :=
    allocatedUniformChartLog_nonneg ((show (0 : ℝ) ≤ M from Nat.cast_nonneg M))
  have hq : 0 ≤ q := by dsimp [q, preparedCanonicalFreezeLog]; positivity
  have hpq : p ≤ q := by dsimp [q, preparedCanonicalFreezeLog]; linarith [(show (0 : ℝ) ≤ M from Nat.cast_nonneg M), (show (0 : ℝ) ≤ m from Nat.cast_nonneg m)]
  have hMq : (M : ℝ) ≤ q := by dsimp [q, preparedCanonicalFreezeLog]; linarith [(show (0 : ℝ) ≤ m from Nat.cast_nonneg m)]
  have hmq : (m : ℝ) ≤ q := by dsimp [q, preparedCanonicalFreezeLog]; linarith [(show (0 : ℝ) ≤ M from Nat.cast_nonneg M)]
  have hCq : allocatedUniformChartLog (M : ℝ) ≤ q := by
    dsimp [q, preparedCanonicalFreezeLog]; linarith [(show (0 : ℝ) ≤ M from Nat.cast_nonneg M), (show (0 : ℝ) ≤ m from Nat.cast_nonneg m)]
  have hqexp : q ≤ Real.exp q := by linarith [Real.add_one_le_exp q]
  have hD : (D : ℝ) ≤ Real.exp q := by
    have hd := (relativePatchComplexity_rank_le A).trans hA
    have hd' : (D : ℝ) ≤ p := by push_cast at hd; linarith [(show (0 : ℝ) ≤ E from Nat.cast_nonneg E)]
    exact hd'.trans (hpq.trans hqexp)
  have hLip : (A.kernel.lip : ℝ) ≤ Real.exp q := by
    have hlog : Real.log (1 + (A.kernel.lip : ℝ)) ≤ p := by
      unfold relativePatchComplexity at hA
      have hrank0 : (0 : ℝ) ≤ (D + E : ℕ) := Nat.cast_nonneg _
      exact (le_add_of_nonneg_left hrank0).trans hA
    have he := Real.exp_le_exp.mpr hlog
    rw [Real.exp_log (by positivity)] at he
    linarith [Real.exp_le_exp.mpr hpq]
  have hcoord j : (Fintype.card (L j).Coord : ℝ) ≤ Real.exp q :=
    (Nat.cast_le.mpr (hM j)).trans (hMq.trans hqexp)
  have hchart := Real.exp_le_exp.mpr hCq
  have hg : Real.exp (-q) ≤ gain := (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans hgain
  have hb j := preparedFreezingEarlyLogBudget hq (NNReal.coe_nonneg A.kernel.lip)
    (Real.exp_nonneg _) hD (hmq.trans hqexp) hLip (hcoord j) hchart hg hδ
  refine ⟨hq, hD, hmq.trans hqexp, hLip, hcoord, hchart, hg,
    fun j => (hb j).1, ?_⟩
  exact (preparedFreezingEarlyLogBudget (N := 0) (C := 0) hq
    (NNReal.coe_nonneg A.kernel.lip) le_rfl hD (hmq.trans hqexp) hLip
    (by simpa using Real.exp_nonneg q) (Real.exp_nonneg q) hg hδ).2

end Erdos3

end

end OAI
