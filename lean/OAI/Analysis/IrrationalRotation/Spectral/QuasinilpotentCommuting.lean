import OAI.Analysis.IrrationalRotation.Model.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

namespace OAI

noncomputable section
open Filter
open scoped Topology BigOperators

namespace Invariant233

theorem exists_geometric_bound_of_root_tendsto_zero (u : ℕ → ℝ)
    (hu : ∀ n, 0 ≤ u n)
    (hroot : Tendsto (fun n : ℕ => (u n) ^ (1 / (n : ℝ))) atTop (𝓝 0))
    (r : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ n, u n ≤ C * r ^ n := by
  have hev : ∀ᶠ n : ℕ in atTop, (u n) ^ (1 / (n : ℝ)) < r :=
    (tendsto_order.mp hroot).2 r hr
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hev.and (eventually_gt_atTop 0))
  let C : ℝ := 1 + ∑ k ∈ Finset.range N, u k / r ^ k
  have hsum : 0 ≤ ∑ k ∈ Finset.range N, u k / r ^ k :=
    Finset.sum_nonneg fun k _ => div_nonneg (hu k) (pow_nonneg hr.le k)
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨C, hC, fun n => ?_⟩
  by_cases hn : n < N
  · have hle : u n / r ^ n ≤ ∑ k ∈ Finset.range N, u k / r ^ k :=
      Finset.single_le_sum (fun k _ => div_nonneg (hu k) (pow_nonneg hr.le k))
        (Finset.mem_range.mpr hn)
    have hleC : u n / r ^ n ≤ C := by dsimp [C]; linarith
    exact (div_le_iff₀ (pow_pos hr n)).mp hleC
  · obtain ⟨hsmall, hnpos⟩ := hN n (Nat.le_of_not_gt hn)
    have hpow := pow_le_pow_left₀ (Real.rpow_nonneg (hu n) _) hsmall.le n
    rw [one_div, Real.rpow_inv_natCast_pow (hu n) (Nat.ne_of_gt hnpos)] at hpow
    exact hpow.trans (le_mul_of_one_le_left (pow_nonneg hr.le n) (by dsimp [C]; linarith))

theorem root_tendsto_zero_of_geometric_bounds (u : ℕ → ℝ)
    (hu : ∀ n, 0 ≤ u n)
    (hbound : ∀ r : ℝ, 0 < r → ∃ C : ℝ, 0 < C ∧ ∀ n, u n ≤ C * r ^ n) :
    Tendsto (fun n : ℕ => (u n) ^ (1 / (n : ℝ))) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun n => ha.trans_le (Real.rpow_nonneg (hu n) _)
  · intro ε hε
    obtain ⟨C, hC, hboundC⟩ := hbound (ε / 2) (by positivity)
    have hCroot : Tendsto (fun n : ℕ => C ^ (1 / (n : ℝ))) atTop (𝓝 1) := by
      simpa [Function.comp_def] using (Real.continuousAt_const_rpow hC.ne').tendsto.comp
        (tendsto_one_div_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0))
    have hev : ∀ᶠ n : ℕ in atTop, C ^ (1 / (n : ℝ)) < 2 :=
      (tendsto_order.mp hCroot).2 2 (by norm_num)
    filter_upwards [hev, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
    have hle := Real.rpow_le_rpow (hu n) (hboundC n)
      (by positivity : 0 ≤ 1 / (n : ℝ))
    rw [Real.mul_rpow hC.le (pow_nonneg (by positivity : 0 ≤ ε / 2) n),
      one_div, Real.pow_rpow_inv_natCast (by positivity : 0 ≤ ε / 2)
        (Nat.ne_of_gt hnpos)] at hle
    have hlt := mul_lt_mul_of_pos_right hn (by positivity : 0 < ε / 2)
    have hlt' : C ^ ((n : ℝ)⁻¹) * (ε / 2) < ε := by
      simpa only [one_div, mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hlt
    simpa only [one_div] using hle.trans_lt hlt'

variable {A : Type*} [NormedRing A]

theorem NormQuasinilpotent.geometric_bound {a : A} (ha : NormQuasinilpotent a)
    (r : ℝ) (hr : 0 < r) : ∃ C : ℝ, 0 < C ∧ ∀ n, ‖a ^ n‖ ≤ C * r ^ n :=
  exists_geometric_bound_of_root_tendsto_zero (fun n => ‖a ^ n‖)
    (fun _ => norm_nonneg _) ha r hr

theorem NormQuasinilpotent.mul_of_commute {a b : A}
    (ha : NormQuasinilpotent a) (hb : NormQuasinilpotent b) (hab : Commute a b) :
    NormQuasinilpotent (a * b) := by
  apply root_tendsto_zero_of_geometric_bounds _ (fun _ => norm_nonneg _)
  intro r hr
  obtain ⟨Ca, hCa, haC⟩ := ha.geometric_bound r hr
  obtain ⟨Cb, hCb, hbC⟩ := hb.geometric_bound 1 zero_lt_one
  refine ⟨Ca * Cb, mul_pos hCa hCb, fun n => ?_⟩
  rw [hab.mul_pow]
  calc
    ‖a ^ n * b ^ n‖ ≤ ‖a ^ n‖ * ‖b ^ n‖ := norm_mul_le _ _
    _ ≤ (Ca * r ^ n) * (Cb * 1 ^ n) :=
      mul_le_mul (haC n) (hbC n) (norm_nonneg _) (by positivity)
    _ = Ca * Cb * r ^ n := by ring

theorem norm_add_pow_le_of_geometric_bounds {a b : A} (hab : Commute a b)
    {Ca Cb r : ℝ} (hCa : 0 ≤ Ca) (_hCb : 0 ≤ Cb) (hr : 0 ≤ r)
    (ha : ∀ n, ‖a ^ n‖ ≤ Ca * r ^ n)
    (hb : ∀ n, ‖b ^ n‖ ≤ Cb * r ^ n) (n : ℕ) :
    ‖(a + b) ^ n‖ ≤ Ca * Cb * (2 * r) ^ n := by
  have hexp : (a + b) ^ n = ∑ k ∈ Finset.range (n + 1),
      n.choose k • (a ^ k * b ^ (n - k)) := by
    simpa only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] using hab.add_pow' n
  rw [hexp]
  calc
    ‖∑ k ∈ Finset.range (n + 1), n.choose k • (a ^ k * b ^ (n - k))‖
        ≤ ∑ k ∈ Finset.range (n + 1), ‖n.choose k • (a ^ k * b ^ (n - k))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℝ) * ((Ca * r ^ k) * (Cb * r ^ (n - k))) := by
      apply Finset.sum_le_sum
      intro k hk
      exact norm_nsmul_le.trans (mul_le_mul_of_nonneg_left
        ((norm_mul_le _ _).trans (mul_le_mul (ha k) (hb (n - k))
          (norm_nonneg _) (mul_nonneg hCa (pow_nonneg hr _)))) (Nat.cast_nonneg _))
    _ = Ca * Cb * (∑ k ∈ Finset.range (n + 1),
        r ^ k * r ^ (n - k) * (n.choose k : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = Ca * Cb * (2 * r) ^ n := by rw [← add_pow]; congr 2; ring

theorem NormQuasinilpotent.add_of_commute {a b : A}
    (ha : NormQuasinilpotent a) (hb : NormQuasinilpotent b) (hab : Commute a b) :
    NormQuasinilpotent (a + b) := by
  apply root_tendsto_zero_of_geometric_bounds _ (fun _ => norm_nonneg _)
  intro r hr
  obtain ⟨Ca, hCa, haC⟩ := ha.geometric_bound (r / 2) (by positivity)
  obtain ⟨Cb, hCb, hbC⟩ := hb.geometric_bound (r / 2) (by positivity)
  refine ⟨Ca * Cb, mul_pos hCa hCb, fun n => ?_⟩
  convert norm_add_pow_le_of_geometric_bounds hab hCa.le hCb.le
    (by positivity : 0 ≤ r / 2) haC hbC n using 1
  ring

end Invariant233

end

end OAI
