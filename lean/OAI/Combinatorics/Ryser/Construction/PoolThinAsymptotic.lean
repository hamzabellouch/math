import OAI.Combinatorics.Ryser.Construction.PoolThinProbability
import OAI.Combinatorics.Ryser.Construction.GroupBounds
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp

namespace OAI

open Filter Topology
open scoped Classical
noncomputable section

namespace RyserCoveringCounterexample.Construction

def thinFailureConstant (s K : ℕ) : ℝ := 128 * (K : ℝ) ^ 6 * (s : ℝ) ^ 12

theorem thinFailureBound_le (s K N : ℕ) {q : ℝ} (hq : 1 ≤ q)
    (hN : (N : ℝ) * (s - 1 : ℕ) ≤ 2 * q) :
    q ^ 3 * (q + 1) * (N : ℝ) ^ 6 *
        ((K : ℝ) * (s ^ 2 : ℕ) * (s - 1 : ℕ) / q ^ 2) ^ 6 ≤
      thinFailureConstant s K / q ^ 2 := by
  have hqpos : 0 < q := by linarith
  have hqne : q ≠ 0 := hqpos.ne'
  have hbase : (N : ℝ) * ((K : ℝ) * (s ^ 2 : ℕ) * (s - 1 : ℕ) / q ^ 2) ≤
      2 * (K : ℝ) * (s : ℝ) ^ 2 / q := by
    calc
      _ = (K : ℝ) * (s : ℝ) ^ 2 * ((N : ℝ) * (s - 1 : ℕ)) / q ^ 2 := by
        push_cast
        ring
      _ ≤ (K : ℝ) * (s : ℝ) ^ 2 * (2 * q) / q ^ 2 := by
        apply div_le_div_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left hN (by positivity)
        · positivity
      _ = 2 * (K : ℝ) * (s : ℝ) ^ 2 / q := by
        field_simp [hqne]
  have hfactor : q ^ 3 * (q + 1) ≤ 2 * q ^ 4 := by
    calc
      _ ≤ q ^ 3 * (2 * q) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 2 * q ^ 4 := by ring
  calc
    _ = q ^ 3 * (q + 1) *
        ((N : ℝ) * ((K : ℝ) * (s ^ 2 : ℕ) * (s - 1 : ℕ) / q ^ 2)) ^ 6 := by
      rw [mul_pow]
      ring
    _ ≤ q ^ 3 * (q + 1) * (2 * (K : ℝ) * (s : ℝ) ^ 2 / q) ^ 6 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase 6) (by positivity)
    _ ≤ 2 * q ^ 4 * (2 * (K : ℝ) * (s : ℝ) ^ 2 / q) ^ 6 :=
      mul_le_mul_of_nonneg_right hfactor (by positivity)
    _ = thinFailureConstant s K / q ^ 2 := by
      unfold thinFailureConstant
      field_simp [hqne]
      ring

theorem tendsto_thinFailureBound (s K : ℕ) :
    Tendsto (fun q : ℕ => thinFailureConstant s K / (q : ℝ) ^ 2) atTop (𝓝 0) := by
  have h : Tendsto (fun q : ℝ => thinFailureConstant s K / q ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0))
  exact h.comp tendsto_natCast_atTop_atTop

theorem exists_thinFailure_cutoff (s K : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → thinFailureConstant s K / (q : ℝ) ^ 2 ≤ η := by
  exact Filter.eventually_atTop.mp ((tendsto_thinFailureBound s K).eventually_le_const hη)

variable {k F : Type*} [Field k] [Field F] [Fintype k] [Fintype F]
variable [DecidableEq k] [DecidableEq F]

theorem prob_groupPoolThin_ge (σ : k →+* F) (u v : k) (huv : u ≠ v) (K : ℕ) :
    1 - thinFailureConstant (Fintype.card k) K / (Fintype.card F : ℝ) ^ 2 ≤
      (poolThinLaw (F := F) (ConfigurationGroup σ) K).prob
        (PoolThin (groupPoints σ u v huv) (groupAltered σ u v huv)) := by
  have hraw := prob_not_poolThin_le (K := K)
    (groupPoints σ u v huv) (groupAltered σ u v huv)
    (Fintype.card k ^ 2) (Fintype.card k - 1)
    (fun i => le_of_eq (groupPoints_card σ u v huv i))
    (fun i => le_of_eq (groupAltered_card σ u v huv i))
  have hq : (1 : ℝ) ≤ Fintype.card F := by
    exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos (α := F)))
  have hN : (Fintype.card (ConfigurationGroup σ) : ℝ) * (Fintype.card k - 1 : ℕ) ≤
      2 * (Fintype.card F : ℝ) := by
    exact_mod_cast card_groups_mul_sub_one_le σ
  have hbound := hraw.trans
    (thinFailureBound_le (Fintype.card k) K (Fintype.card (ConfigurationGroup σ)) hq hN)
  rw [FiniteLaw.prob_compl] at hbound
  linarith

end RyserCoveringCounterexample.Construction

end

end OAI
