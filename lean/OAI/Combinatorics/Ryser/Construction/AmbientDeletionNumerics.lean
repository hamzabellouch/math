import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

open scoped BigOperators

namespace RyserCoveringCounterexample.Construction

noncomputable def ambientDeletionDelta (s K : ℕ) : ℝ :=
  Real.exp (-4 * (K : ℝ) * ((s - 1 : ℕ) : ℝ))

theorem ambientDeletionDelta_pos (s K : ℕ) : 0 < ambientDeletionDelta s K :=
  Real.exp_pos _

theorem ambientDeletionDelta_lt_one (s K : ℕ) (hs : 2 ≤ s) (hK : 0 < K) :
    ambientDeletionDelta s K < 1 := by
  have hK' : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hm : (0 : ℝ) < ((s - 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 1 < 2) hs)
  unfold ambientDeletionDelta
  apply Real.exp_lt_one_iff.mpr
  have hpos : (0 : ℝ) < 4 * (K : ℝ) * ((s - 1 : ℕ) : ℝ) :=
    mul_pos (mul_pos (by norm_num) hK') hm
  nlinarith only [hpos]

theorem neg_two_mul_le_log_one_sub {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    -2 * t ≤ Real.log (1 - t) := by
  have hb : 0 < 1 - t := by linarith
  have hratio : t / (1 - t) ≤ 2 * t := by
    apply (div_le_iff₀ hb).2
    have hmul := mul_nonneg ht0 (show 0 ≤ 1 - 2 * t by linarith)
    nlinarith only [hmul]
  have hid : 1 - (1 - t)⁻¹ = -(t / (1 - t)) := by
    field_simp [hb.ne']
    ring
  calc
    -2 * t ≤ -(t / (1 - t)) := by linarith only [hratio]
    _ = 1 - (1 - t)⁻¹ := hid.symm
    _ ≤ Real.log (1 - t) := Real.one_sub_inv_le_log_of_pos hb

theorem exp_neg_two_mul_le_one_sub_pow (N : ℕ) {t : ℝ}
    (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    Real.exp (-2 * (N : ℝ) * t) ≤ (1 - t) ^ N := by
  have hb : 0 < 1 - t := by linarith
  apply (Real.le_log_iff_exp_le (pow_pos hb N)).mp
  rw [Real.log_pow]
  have hlog := mul_le_mul_of_nonneg_left (neg_two_mul_le_log_one_sub ht0 ht)
    (Nat.cast_nonneg N : (0 : ℝ) ≤ (N : ℝ))
  nlinarith only [hlog]

theorem ambientDeletionDelta_le_pow (s K q N : ℕ) (hs : 2 ≤ s) (hq : 0 < q)
    (hsmall : 2 * (s - 1) ^ 2 ≤ q) (hcount : N * (s - 1) ≤ 2 * K * q) :
    ambientDeletionDelta s K ≤ (1 - ((s - 1 : ℕ) : ℝ) ^ 2 / (q : ℝ)) ^ N := by
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hm : (0 : ℝ) < ((s - 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 1 < 2) hs)
  have hsmall' : (2 : ℝ) * ((s - 1 : ℕ) : ℝ) ^ 2 ≤ (q : ℝ) := by
    exact_mod_cast hsmall
  have hcount' : (N : ℝ) * ((s - 1 : ℕ) : ℝ) ≤ 2 * (K : ℝ) * (q : ℝ) := by
    exact_mod_cast hcount
  let t : ℝ := ((s - 1 : ℕ) : ℝ) ^ 2 / (q : ℝ)
  have ht0 : 0 ≤ t := div_nonneg (sq_nonneg _) hq'.le
  have ht : t ≤ 1 / 2 := by
    apply (div_le_iff₀ hq').2
    nlinarith only [hsmall']
  have htotal : (N : ℝ) * t ≤ 2 * (K : ℝ) * ((s - 1 : ℕ) : ℝ) := by
    dsimp only [t]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hq').2
    have hmul := mul_le_mul_of_nonneg_right hcount' hm.le
    nlinarith only [hmul]
  have hexponent : -4 * (K : ℝ) * ((s - 1 : ℕ) : ℝ) ≤ -2 * (N : ℝ) * t := by
    nlinarith only [htotal]
  unfold ambientDeletionDelta
  exact (Real.exp_le_exp.mpr hexponent).trans
    (exp_neg_two_mul_le_one_sub_pow N ht0 ht)

theorem ambientDeletionDelta_le_finset_prod {ι : Type*} (I : Finset ι)
    (s K q : ℕ) (hs : 2 ≤ s) (hq : 0 < q) (hsmall : 2 * (s - 1) ^ 2 ≤ q)
    (hcount : I.card * (s - 1) ≤ 2 * K * q) (p : ι → ℝ)
    (hp : ∀ i ∈ I, p i ≤ ((s - 1 : ℕ) : ℝ) ^ 2 / (q : ℝ)) :
    ambientDeletionDelta s K ≤ ∏ i ∈ I, (1 - p i) := by
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hsmall' : (2 : ℝ) * ((s - 1 : ℕ) : ℝ) ^ 2 ≤ (q : ℝ) := by
    exact_mod_cast hsmall
  have hhalf : ((s - 1 : ℕ) : ℝ) ^ 2 / (q : ℝ) ≤ 1 / 2 := by
    apply (div_le_iff₀ hq').2
    nlinarith only [hsmall']
  have hbase : 0 ≤ 1 - ((s - 1 : ℕ) : ℝ) ^ 2 / (q : ℝ) := by linarith
  apply (ambientDeletionDelta_le_pow s K q I.card hs hq hsmall hcount).trans
  calc
    (1 - ((s - 1 : ℕ) : ℝ) ^ 2 / (q : ℝ)) ^ I.card =
        ∏ _i ∈ I, (1 - ((s - 1 : ℕ) : ℝ) ^ 2 / (q : ℝ)) := by
      rw [Finset.prod_const]
    _ ≤ ∏ i ∈ I, (1 - p i) :=
      Finset.prod_le_prod₀ (fun _ _ => hbase)
        (fun i hi => sub_le_sub_left (hp i hi) 1)

theorem ambientDeletionDelta_le_prod {ι : Type*} [Fintype ι]
    (s K q : ℕ) (hs : 2 ≤ s) (hq : 0 < q) (hsmall : 2 * (s - 1) ^ 2 ≤ q)
    (hcount : Fintype.card ι * (s - 1) ≤ 2 * K * q) (p : ι → ℝ)
    (hp : ∀ i, p i ≤ ((s - 1 : ℕ) : ℝ) ^ 2 / (q : ℝ)) :
    ambientDeletionDelta s K ≤ ∏ i, (1 - p i) := by
  classical
  apply ambientDeletionDelta_le_finset_prod Finset.univ s K q hs hq hsmall ?_ p ?_
  · simpa only [Finset.card_univ] using hcount
  · intro i _
    exact hp i

end RyserCoveringCounterexample.Construction

end OAI
