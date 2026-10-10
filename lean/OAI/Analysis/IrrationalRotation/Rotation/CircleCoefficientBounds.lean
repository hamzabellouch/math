import OAI.Analysis.IrrationalRotation.Rotation.CircleParameterBlocks
import Mathlib.Topology.Algebra.InfiniteSum.Order

namespace OAI

noncomputable section
open scoped BigOperators

namespace Invariant233.CircleParameterLaws
open CircleParameterData
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem sum_flattenedCost_prefix (j : ℕ) :
    (∑ n ∈ Finset.range (p.blockEnd j), p.flattenedCost n) =
      ∑ s ∈ Finset.Icc 1 j, p.C s * (p.m s : ℝ) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [p.blockEnd_succ, Finset.sum_range_add, ih,
        Finset.sum_Icc_succ_top (by omega)]
      congr 1
      have hcost : ∀ n ∈ Finset.range (p.m (j + 1)),
          p.flattenedCost (p.blockEnd j + n) = p.C (j + 1) := by
        intro n hn
        apply p.flattenedCost_eq_of_mem hp.m_pos
        rw [p.mem_block_iff]
        simp only [Nat.add_sub_cancel, p.blockEnd_succ]
        have hn' := Finset.mem_range.mp hn
        omega
      calc
        (∑ n ∈ Finset.range (p.m (j + 1)),
            p.flattenedCost (p.blockEnd j + n)) =
            ∑ _n ∈ Finset.range (p.m (j + 1)), p.C (j + 1) :=
          Finset.sum_congr rfl hcost
        _ = _ := by simp [mul_comm]

theorem coefficientBound_eq_prefix (j : ℕ) :
    p.coefficientBound j = Real.exp (((p.K j : ℝ) + 1) *
      ∑ n ∈ Finset.range (p.blockEnd (j - 1)), p.flattenedCost n) := by
  rw [hp.sum_flattenedCost_prefix]
  rfl

theorem exists_future_block (j n : ℕ) (hn : p.blockEnd (j - 1) ≤ n) :
    ∃ s : ℕ, j ≤ s ∧ 1 ≤ s ∧ n + 1 ∈ p.block s := by
  obtain ⟨s, hs, hns⟩ := p.exists_mem_block hp.m_pos (n + 1) (by omega)
  refine ⟨s, ?_, hs, hns⟩
  by_contra h
  have hsj : s ≤ j - 1 := by omega
  have hends := (p.blockEnd_strictMono hp.m_pos).monotone hsj
  have hmem := (p.mem_block_iff s (n + 1)).mp hns
  omega

theorem floor_add_eq_zero_of_upper_exclusion (j s i v : ℕ)
    (hs : 1 ≤ s) (hi : i ∈ p.block s) (hv : v ≤ p.K j)
    (x : ℝ) (hx0 : 0 ≤ x) (hx : x < 1 - 2 * (p.K j : ℝ) / p.N s) :
    ⌊x + (v : ℝ) * p.alpha θ i⌋ = 0 := by
  have ha0 : 0 ≤ p.alpha θ i := Int.fract_nonneg _
  have hahi := (hp.phase_bounds s hs i hi).2.le
  apply Int.floor_eq_zero_iff.mpr
  constructor
  · exact add_nonneg hx0 (mul_nonneg (Nat.cast_nonneg _) ha0)
  · have hv' : (v : ℝ) ≤ p.K j := by exact_mod_cast hv
    have hmul := mul_le_mul hv' hahi ha0 (Nat.cast_nonneg _)
    have he : (p.K j : ℝ) * (2 / p.N s) = 2 * (p.K j : ℝ) / p.N s := by ring
    rw [he] at hmul
    linarith

theorem floor_sub_eq_zero_of_lower_exclusion (j s i v : ℕ)
    (hs : 1 ≤ s) (hi : i ∈ p.block s) (hv : v ≤ p.K j)
    (y : ℝ) (hy1 : y < 1) (hy : 2 * (p.K j : ℝ) / p.N s < y) :
    ⌊y - (v : ℝ) * p.alpha θ i⌋ = 0 := by
  have ha0 : 0 ≤ p.alpha θ i := Int.fract_nonneg _
  have hahi := (hp.phase_bounds s hs i hi).2.le
  have hv' : (v : ℝ) ≤ p.K j := by exact_mod_cast hv
  have hmul := mul_le_mul hv' hahi ha0 (Nat.cast_nonneg _)
  have he : (p.K j : ℝ) * (2 / p.N s) = 2 * (p.K j : ℝ) / p.N s := by ring
  rw [he] at hmul
  apply Int.floor_eq_zero_iff.mpr
  constructor
  · nlinarith
  · have hnonneg := mul_nonneg (Nat.cast_nonneg v : (0 : ℝ) ≤ v) ha0
    linarith

theorem future_floor_add_zero (j v : ℕ) (hv : v ≤ p.K j) (u : ℕ → ℝ)
    (hu0 : ∀ i, 0 ≤ u i)
    (hexcl : ∀ s, j ≤ s → 1 ≤ s → ∀ i ∈ p.block s,
      u i < 1 - 2 * (p.K j : ℝ) / p.N s) :
    ∀ n, p.blockEnd (j - 1) ≤ n →
      ⌊u (n + 1) + (v : ℝ) * p.alpha θ (n + 1)⌋ = 0 := by
  intro n hn
  obtain ⟨s, hjs, hs, hns⟩ := hp.exists_future_block j n hn
  exact hp.floor_add_eq_zero_of_upper_exclusion j s (n + 1) v hs hns hv
    (u (n + 1)) (hu0 _) (hexcl s hjs hs _ hns)

theorem future_floor_sub_zero (j v : ℕ) (hv : v ≤ p.K j) (u : ℕ → ℝ)
    (hu1 : ∀ i, u i < 1)
    (hexcl : ∀ s, j ≤ s → 1 ≤ s → ∀ i ∈ p.block s,
      2 * (p.K j : ℝ) / p.N s < u i) :
    ∀ n, p.blockEnd (j - 1) ≤ n →
      ⌊u (n + 1) - (v : ℝ) * p.alpha θ (n + 1)⌋ = 0 := by
  intro n hn
  obtain ⟨s, hjs, hs, hns⟩ := hp.exists_future_block j n hn
  exact hp.floor_sub_eq_zero_of_lower_exclusion j s (n + 1) v hs hns hv
    (u (n + 1)) (hu1 _) (hexcl s hjs hs _ hns)

theorem weighted_floor_add_eq_prefix (j v : ℕ) (hv : v ≤ p.K j) (u : ℕ → ℝ)
    (hu0 : ∀ i, 0 ≤ u i)
    (hexcl : ∀ s, j ≤ s → 1 ≤ s → ∀ i ∈ p.block s,
      u i < 1 - 2 * (p.K j : ℝ) / p.N s) :
    (∑' n, p.flattenedCost n *
      (⌊u (n + 1) + (v : ℝ) * p.alpha θ (n + 1)⌋ : ℝ)) =
    ∑ n ∈ Finset.range (p.blockEnd (j - 1)), p.flattenedCost n *
      (⌊u (n + 1) + (v : ℝ) * p.alpha θ (n + 1)⌋ : ℝ) := by
  apply tsum_eq_sum
  intro n hn
  have hn' : p.blockEnd (j - 1) ≤ n := by simpa using hn
  rw [hp.future_floor_add_zero j v hv u hu0 hexcl n hn']
  simp

theorem weighted_floor_sub_eq_prefix (j v : ℕ) (hv : v ≤ p.K j) (u : ℕ → ℝ)
    (hu1 : ∀ i, u i < 1)
    (hexcl : ∀ s, j ≤ s → 1 ≤ s → ∀ i ∈ p.block s,
      2 * (p.K j : ℝ) / p.N s < u i) :
    (∑' n, p.flattenedCost n *
      (⌊u (n + 1) - (v : ℝ) * p.alpha θ (n + 1)⌋ : ℝ)) =
    ∑ n ∈ Finset.range (p.blockEnd (j - 1)), p.flattenedCost n *
      (⌊u (n + 1) - (v : ℝ) * p.alpha θ (n + 1)⌋ : ℝ) := by
  apply tsum_eq_sum
  intro n hn
  have hn' : p.blockEnd (j - 1) ≤ n := by simpa using hn
  rw [hp.future_floor_sub_zero j v hv u hu1 hexcl n hn']
  simp

theorem exp_weighted_floor_add_le_coefficientBound (j v : ℕ) (hv : v ≤ p.K j)
    (u : ℕ → ℝ) (hu : ∀ i, u i ∈ Set.Ico (0 : ℝ) 1)
    (hexcl : ∀ s, j ≤ s → 1 ≤ s → ∀ i ∈ p.block s,
      u i < 1 - 2 * (p.K j : ℝ) / p.N s) :
    Real.exp (∑' n, p.flattenedCost n *
      (⌊u (n + 1) + (v : ℝ) * p.alpha θ (n + 1)⌋ : ℝ)) ≤
      p.coefficientBound j := by
  rw [hp.weighted_floor_add_eq_prefix j v hv u (fun i => (hu i).1) hexcl,
    hp.coefficientBound_eq_prefix]
  apply Real.exp_le_exp.mpr
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n _
  have hc : 0 ≤ p.flattenedCost n :=
    (hp.C_pos _ (p.blockIndex_pos hp.m_pos (by omega))).le
  have hfloor :
      (⌊u (n + 1) + (v : ℝ) * p.alpha θ (n + 1)⌋ : ℝ) ≤ (p.K j : ℝ) + 1 := by
    have hf := Int.floor_le (u (n + 1) + (v : ℝ) * p.alpha θ (n + 1))
    have ha : p.alpha θ (n + 1) < 1 := Int.fract_lt_one _
    have hv' : (v : ℝ) ≤ p.K j := by exact_mod_cast hv
    have hv0 : (0 : ℝ) ≤ v := Nat.cast_nonneg _
    have hu1 := (hu (n + 1)).2
    nlinarith
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hfloor hc

theorem exp_neg_weighted_floor_sub_le_coefficientBound (j v : ℕ)
    (hv : v ≤ p.K j) (u : ℕ → ℝ) (hu : ∀ i, u i ∈ Set.Ico (0 : ℝ) 1)
    (hexcl : ∀ s, j ≤ s → 1 ≤ s → ∀ i ∈ p.block s,
      2 * (p.K j : ℝ) / p.N s < u i) :
    Real.exp (-(∑' n, p.flattenedCost n *
      (⌊u (n + 1) - (v : ℝ) * p.alpha θ (n + 1)⌋ : ℝ))) ≤
      p.coefficientBound j := by
  rw [hp.weighted_floor_sub_eq_prefix j v hv u (fun i => (hu i).2) hexcl,
    hp.coefficientBound_eq_prefix]
  apply Real.exp_le_exp.mpr
  rw [← Finset.sum_neg_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n _
  have hc : 0 ≤ p.flattenedCost n :=
    (hp.C_pos _ (p.blockIndex_pos hp.m_pos (by omega))).le
  have hfloor :
      -(⌊u (n + 1) - (v : ℝ) * p.alpha θ (n + 1)⌋ : ℝ) ≤ (p.K j : ℝ) + 1 := by
    have hf := Int.lt_floor_add_one (u (n + 1) - (v : ℝ) * p.alpha θ (n + 1))
    have ha : p.alpha θ (n + 1) < 1 := Int.fract_lt_one _
    have hv' : (v : ℝ) ≤ p.K j := by exact_mod_cast hv
    have hv0 : (0 : ℝ) ≤ v := Nat.cast_nonneg _
    have hu0 := (hu (n + 1)).1
    nlinarith
  simpa only [mul_neg, neg_mul, mul_comm] using mul_le_mul_of_nonneg_left hfloor hc

end Invariant233.CircleParameterLaws

end

end OAI
