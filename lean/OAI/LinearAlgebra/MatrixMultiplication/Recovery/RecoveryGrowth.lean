import OAI.LinearAlgebra.MatrixMultiplication.Separation.FiniteCover
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

/-! Finite orbit symmetries, masks and exact recovery operations. -/

noncomputable section

namespace MatrixMultiplication.RecoveryGrowth

open Filter
open scoped Topology BigOperators

def shiftCount (b C : ℝ) (N : ℕ) : ℕ :=
  ⌈(b + 1) * (N : ℝ) / Real.log ((N : ℝ) / (3 * C))⌉₊

def replicationCount (b C : ℝ) (N : ℕ) : ℕ :=
  2 ^ (3 * shiftCount b C N)

theorem shiftCount_pos {b C : ℝ} {N : ℕ}
    (hb : 0 ≤ b) (hC : 0 < C) (hN : 3 * C < (N : ℝ)) :
    0 < shiftCount b C N := by
  have hC3 : 0 < 3 * C := by linarith
  have hN0 : 0 < (N : ℝ) := hC3.trans hN
  have hlog : 0 < Real.log ((N : ℝ) / (3 * C)) :=
    Real.log_pos ((one_lt_div hC3).2 hN)
  exact Nat.ceil_pos.2 (div_pos (mul_pos (by linarith) hN0) hlog)

theorem support_loss_bound {b C : ℝ} {N : ℕ}
    (hC : 0 < C) (hN : 3 * C < (N : ℝ)) :
    Real.exp (b * N) * (3 * C / (N : ℝ)) ^ shiftCount b C N ≤
      Real.exp (-(N : ℝ)) := by
  have hC3 : 0 < 3 * C := by linarith
  have hN0 : 0 < (N : ℝ) := hC3.trans hN
  have hlog : 0 < Real.log ((N : ℝ) / (3 * C)) :=
    Real.log_pos ((one_lt_div hC3).2 hN)
  have hceil : (b + 1) * (N : ℝ) ≤
      (shiftCount b C N : ℝ) * Real.log ((N : ℝ) / (3 * C)) := by
    exact (div_le_iff₀ hlog).1 (Nat.le_ceil _)
  have hbase : 3 * C / (N : ℝ) =
      Real.exp (-Real.log ((N : ℝ) / (3 * C))) := by
    rw [Real.exp_neg, Real.exp_log (div_pos hN0 hC3)]
    simp
  rw [hbase, ← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem cardinal_budget {b C : ℝ} {N S t g : ℕ}
    (hC : 0 < C) (hN : 3 * C < (N : ℝ)) (hg : 0 < g)
    (hS : (S : ℝ) ≤ Real.exp (b * N))
    (ht : (t : ℝ) / (g : ℝ) ≤ 3 * C / (N : ℝ)) :
    S * t ^ shiftCount b C N < g ^ shiftCount b C N := by
  have hgr : 0 < (g : ℝ) := by exact_mod_cast hg
  have hN0 : 0 < (N : ℝ) := by linarith
  have hpow := pow_le_pow_left₀
    (div_nonneg (Nat.cast_nonneg t) hgr.le) ht (shiftCount b C N)
  have hprob : (S : ℝ) * ((t : ℝ) / (g : ℝ)) ^ shiftCount b C N < 1 := by
    calc
      (S : ℝ) * ((t : ℝ) / (g : ℝ)) ^ shiftCount b C N ≤
          Real.exp (b * N) * (3 * C / (N : ℝ)) ^ shiftCount b C N :=
        mul_le_mul hS hpow (pow_nonneg (div_nonneg (Nat.cast_nonneg t) hgr.le) _)
          (Real.exp_pos _).le
      _ ≤ Real.exp (-(N : ℝ)) := support_loss_bound hC hN
      _ < 1 := by rw [Real.exp_lt_one_iff]; linarith
  rw [div_pow, ← mul_div_assoc] at hprob
  have hreal := (div_lt_iff₀ (pow_pos hgr (shiftCount b C N))).1 hprob
  simp only [one_mul] at hreal
  exact_mod_cast hreal

theorem exists_cover {M G : Type*} [Fintype G] [Nonempty G]
    [DecidableEq G] [DecidableEq M]
    (s : Finset M) (good : G → M → Prop) [∀ g, DecidablePred (good g)]
    {b C : ℝ} {N : ℕ} (hC : 0 < C) (hN : 3 * C < (N : ℝ))
    (hs : (s.card : ℝ) ≤ Real.exp (b * N))
    (hbad : ∀ m ∈ s,
      ((Finset.univ.filter fun g => ¬good g m).card : ℝ) / Fintype.card G ≤
        3 * C / (N : ℝ)) :
    ∃ f : Fin (shiftCount b C N) → G, ∀ m ∈ s, ∃ i, good (f i) m := by
  let t := ⌊(3 * C / (N : ℝ)) * Fintype.card G⌋₊
  have hg : 0 < (Fintype.card G : ℝ) := by exact_mod_cast Fintype.card_pos
  have harg : 0 ≤ (3 * C / (N : ℝ)) * Fintype.card G := by
    exact mul_nonneg (div_nonneg (by linarith) (Nat.cast_nonneg N)) hg.le
  apply FiniteCover.exists_cover s good t (shiftCount b C N)
  · intro m hm
    exact Nat.le_floor ((div_le_iff₀ hg).1 (hbad m hm))
  · apply cardinal_budget hC hN Fintype.card_pos hs
    exact (div_le_iff₀ hg).2 (Nat.floor_le harg)

theorem shiftCount_div_nat_le {b C : ℝ} {N : ℕ}
    (hb : 0 < b) (hC : 0 < C) (hN : 3 * C < (N : ℝ)) :
    (shiftCount b C N : ℝ) / (N : ℝ) ≤
      (b + 1) / Real.log ((N : ℝ) / (3 * C)) + 1 / (N : ℝ) := by
  have hC3 : 0 < 3 * C := by linarith
  have hN0 : 0 < (N : ℝ) := hC3.trans hN
  have hlog : 0 < Real.log ((N : ℝ) / (3 * C)) :=
    Real.log_pos ((one_lt_div hC3).2 hN)
  have harg : 0 ≤ (b + 1) * (N : ℝ) / Real.log ((N : ℝ) / (3 * C)) :=
    div_nonneg (mul_nonneg (by linarith) hN0.le) hlog.le
  have hceil := div_le_div_of_nonneg_right (Nat.ceil_lt_add_one harg).le hN0.le
  change (shiftCount b C N : ℝ) / (N : ℝ) ≤ _ at hceil
  convert hceil using 1
  field_simp [hN0.ne', hlog.ne']

theorem tendsto_shiftCount_div_nat {b C : ℝ} (hb : 0 < b) (hC : 0 < C) :
    Tendsto (fun N : ℕ => (shiftCount b C N : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun N : ℕ => Real.log ((N : ℝ) / (3 * C))) atTop atTop :=
    Real.tendsto_log_atTop.comp (hnat.atTop_div_const (by linarith))
  have hmain : Tendsto (fun N : ℕ =>
      (b + 1) / Real.log ((N : ℝ) / (3 * C))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have herr : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hnat
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa only [add_zero] using hmain.add herr)
  · exact Eventually.of_forall fun N => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards [hnat.eventually_gt_atTop (3 * C)] with N hN
    exact shiftCount_div_nat_le hb hC hN

theorem eventually_shiftCount_div_nat_le_log {b C : ℝ} (hb : 0 < b) (hC : 0 < C) :
    ∀ᶠ N : ℕ in atTop, (shiftCount b C N : ℝ) / (N : ℝ) ≤
      (2 * b + 3) / Real.log (N : ℝ) := by
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlognat := Real.tendsto_log_atTop.comp hnat
  filter_upwards [hnat.eventually_gt_atTop (3 * C), hnat.eventually_gt_atTop 1,
    hlognat.eventually_ge_atTop (2 * Real.log (3 * C))] with N hN hN1 hlarge
  change 2 * Real.log (3 * C) ≤ Real.log (N : ℝ) at hlarge
  have hN0 : 0 < (N : ℝ) := lt_trans zero_lt_one hN1
  have hC3 : 0 < 3 * C := by linarith
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hden : 0 < Real.log ((N : ℝ) / (3 * C)) :=
    Real.log_pos ((one_lt_div hC3).2 hN)
  have hhalf : Real.log (N : ℝ) ≤ 2 * Real.log ((N : ℝ) / (3 * C)) := by
    rw [Real.log_div hN0.ne' hC3.ne']
    linarith
  have hmain : (b + 1) / Real.log ((N : ℝ) / (3 * C)) ≤
      (2 * (b + 1)) / Real.log (N : ℝ) := by
    apply (div_le_div_iff₀ hden hlog).2
    nlinarith [mul_le_mul_of_nonneg_left hhalf (show 0 ≤ b + 1 by linarith)]
  have herr : 1 / (N : ℝ) ≤ 1 / Real.log (N : ℝ) :=
    div_le_div_of_nonneg_left zero_le_one hlog (Real.log_le_self hN0.le)
  calc
    (shiftCount b C N : ℝ) / (N : ℝ) ≤
        (b + 1) / Real.log ((N : ℝ) / (3 * C)) + 1 / (N : ℝ) :=
      shiftCount_div_nat_le hb hC hN
    _ ≤ (2 * (b + 1)) / Real.log (N : ℝ) + 1 / Real.log (N : ℝ) :=
      add_le_add hmain herr
    _ = (2 * b + 3) / Real.log (N : ℝ) := by ring

theorem log_replicationCount (b C : ℝ) (N : ℕ) :
    Real.log (replicationCount b C N : ℝ) =
      (3 * Real.log 2) * (shiftCount b C N : ℝ) := by
  simp only [replicationCount, Nat.cast_pow, Real.log_pow, Nat.cast_mul, Nat.cast_ofNat]
  ring

theorem eventually_log_replicationCount_div_nat_le_log {b C : ℝ}
    (hb : 0 < b) (hC : 0 < C) :
    ∀ᶠ N : ℕ in atTop, Real.log (replicationCount b C N : ℝ) / (N : ℝ) ≤
      (3 * Real.log 2 * (2 * b + 3)) / Real.log (N : ℝ) := by
  filter_upwards [eventually_shiftCount_div_nat_le_log hb hC] with N hN
  have hlog2 : 0 ≤ 3 * Real.log 2 :=
    mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num))
  simpa only [log_replicationCount, mul_div_assoc] using
    mul_le_mul_of_nonneg_left hN hlog2

theorem tendsto_log_replicationCount_div_nat {b C : ℝ} (hb : 0 < b) (hC : 0 < C) :
    Tendsto (fun N : ℕ => Real.log (replicationCount b C N : ℝ) / (N : ℝ))
      atTop (𝓝 0) := by
  have h := (tendsto_shiftCount_div_nat hb hC).const_mul (3 * Real.log 2)
  simp only [mul_zero] at h
  convert h using 1
  ext N
  simp only [log_replicationCount]
  ring

theorem eventually_replicationCount_le_exp {b C ε : ℝ}
    (hb : 0 < b) (hC : 0 < C) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (replicationCount b C N : ℝ) ≤ Real.exp (ε * N) := by
  filter_upwards [(tendsto_log_replicationCount_div_nat hb hC).eventually_lt_const hε,
    eventually_gt_atTop (0 : ℕ)] with N hrate hN
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast hN
  have hrep : 0 < (replicationCount b C N : ℝ) := by
    simp only [replicationCount, Nat.cast_pow, Nat.cast_ofNat]
    exact pow_pos (by norm_num) _
  exact (Real.log_le_iff_le_exp hrep).1 ((div_lt_iff₀ hN0).1 hrate).le

theorem tendsto_log_prod_div_nat {J : Type*} (s : Finset J)
    {r : J → ℕ → ℕ}
    (hr : ∀ j ∈ s, ∀ N, 0 < r j N)
    (hlim : ∀ j ∈ s, Tendsto (fun N => Real.log (r j N : ℝ) / (N : ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun N => Real.log ((∏ j ∈ s, r j N : ℕ) : ℝ) / (N : ℝ))
      atTop (𝓝 0) := by
  have hsum := tendsto_finsetSum s hlim
  simp only [Finset.sum_const_zero] at hsum
  apply hsum.congr
  intro N
  rw [Nat.cast_prod, Real.log_prod (s := s) (f := fun j => (r j N : ℝ))
    (fun j hj => Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hr j hj N)))]
  simp only [div_eq_mul_inv, Finset.sum_mul]

end MatrixMultiplication.RecoveryGrowth

end

end OAI
