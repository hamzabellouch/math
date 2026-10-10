import OAI.NumberTheory.JointDickman.Counting.CoefficientProbabilityLoss
import Mathlib.Data.Nat.Log

namespace OAI

/-! # Dyadic boxes covering the amplification coefficients -/

namespace JointDickman

open Filter Finset
open scoped Topology

def coefficientDyadicBox (T k : ℕ) : Finset (ℕ × ℕ) :=
  (Ico (T * 2^k) (4 * T * 2^k)) ×ˢ (Ico (2^k) (2 * 2^k))

def coefficientDyadicCover (B T : ℕ) : Finset (ℕ × ℕ) :=
  (Ico B (4 * B)).biUnion (coefficientDyadicBox T)

theorem coefficientDyadicBox_disjoint (T : ℕ) {k l : ℕ} (hkl : k ≠ l) :
    Disjoint (coefficientDyadicBox T k) (coefficientDyadicBox T l) := by
  have hforward : ∀ k l : ℕ, k < l →
      Disjoint (coefficientDyadicBox T k) (coefficientDyadicBox T l) := by
    intro k l hlt
    apply disjoint_left.mpr
    intro ac hk hl
    have hkc := mem_Ico.mp (mem_product.mp hk).2
    have hlc := mem_Ico.mp (mem_product.mp hl).2
    have hpow := Nat.pow_le_pow_right (by norm_num : 0 < 2) hlt
    rw [pow_succ, mul_comm _ 2] at hpow
    omega
  rcases lt_or_gt_of_ne hkl with h | h
  · exact hforward k l h
  · exact (hforward l k h).symm

open Classical in
noncomputable def amplificationCoefficientPairs (B T : ℕ) : Finset (ℕ × ℕ) :=
  (coefficientDyadicCover B T).filter fun ac =>
    Real.exp (B : ℝ) ≤ ac.2 ∧ (ac.2 : ℝ) ≤ Real.exp (2 * B) ∧
      T * ac.2 ≤ ac.1 ∧ ac.1 < 2 * T * ac.2

theorem nat_two_pow_exp (k : ℕ) :
    ((2^k : ℕ) : ℝ) = Real.exp ((k : ℝ) * Real.log 2) := by
  rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_cast

theorem coefficientDyadicCover_contains {B T a c : ℕ} (hB : 0 < B)
    (hcl : Real.exp (B : ℝ) ≤ c) (hcu : (c : ℝ) ≤ Real.exp (2 * B))
    (ha : T * c ≤ a) (ha' : a < 2 * T * c) :
    (a, c) ∈ coefficientDyadicCover B T := by
  have hc0 : 0 < c := by exact_mod_cast (Real.exp_pos (B : ℝ)).trans_le hcl
  have hcne : c ≠ 0 := Nat.ne_of_gt hc0
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hlo : B ≤ Nat.log 2 c := by
    apply (Nat.le_log_iff_pow_le (by norm_num) hcne).mpr
    have hpow : ((2^B : ℕ) : ℝ) ≤ c := by
      rw [nat_two_pow_exp]
      apply le_trans (Real.exp_le_exp.mpr _) hcl
      nlinarith only [Real.log_two_lt_d9]
    exact_mod_cast hpow
  have hhi : Nat.log 2 c < 4 * B := by
    apply (Nat.log_lt_iff_lt_pow (by norm_num) hcne).mpr
    have hpow : (c : ℝ) < ((2^(4 * B) : ℕ) : ℝ) := by
      rw [nat_two_pow_exp]
      apply lt_of_le_of_lt hcu
      apply Real.exp_lt_exp.mpr
      push_cast
      nlinarith only [Real.log_two_gt_d9, hB0]
    exact_mod_cast hpow
  have hcp := Nat.pow_log_le_self 2 hcne
  have hcp' := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) c
  rw [pow_succ, mul_comm _ 2] at hcp'
  apply mem_biUnion.mpr
  refine ⟨Nat.log 2 c, mem_Ico.mpr ⟨hlo, hhi⟩, ?_⟩
  apply mem_product.mpr
  constructor
  · apply mem_Ico.mpr
    constructor
    · exact (Nat.mul_le_mul_left T hcp).trans ha
    · have hh := Nat.mul_le_mul_left (2 * T) hcp'.le
      nlinarith only [ha', hh]
  · exact mem_Ico.mpr ⟨hcp, hcp'⟩

theorem mem_amplificationCoefficientPairs {B T a c : ℕ} (hB : 0 < B) :
    (a, c) ∈ amplificationCoefficientPairs B T ↔
      Real.exp (B : ℝ) ≤ c ∧ (c : ℝ) ≤ Real.exp (2 * B) ∧
        T * c ≤ a ∧ a < 2 * T * c := by
  classical
  constructor
  · exact fun h => (mem_filter.mp h).2
  · intro h
    exact mem_filter.mpr ⟨coefficientDyadicCover_contains hB h.1 h.2.1 h.2.2.1 h.2.2.2, h⟩

/-- Every box in the cover is long enough for the sieve and remains
inside the coefficient range of the local prime-product law. -/
theorem coefficientDyadicBox_scales :
    ∀ᶠ B : ℕ in atTop, ∀ T k : ℕ, (T : ℝ) ≤ Real.exp ((1 / 10 : ℝ) * B) →
      k ∈ Ico B (4 * B) →
      Real.exp ((1 / 2 : ℝ) * B) ≤ ((2^k : ℕ) : ℝ) ∧
        (4 * T * (2^k : ℕ) : ℝ) ≤ Real.exp ((16 / 5 : ℝ) * B) := by
  have hexp : ∀ᶠ B : ℕ in atTop, (4 : ℝ) ≤ Real.exp ((1 / 10 : ℝ) * B) :=
    (Real.tendsto_exp_atTop.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 10))).eventually_ge_atTop 4
  filter_upwards [hexp, eventually_gt_atTop 0] with B h4 hB
  intro T k hT hk
  have hk' := mem_Ico.mp hk
  have hklo : (B : ℝ) ≤ k := by exact_mod_cast hk'.1
  have hkhi : (k : ℝ) ≤ 4 * B := by exact_mod_cast hk'.2.le
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hlog0 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlow : Real.exp ((1 / 2 : ℝ) * B) ≤ ((2^k : ℕ) : ℝ) := by
    rw [nat_two_pow_exp]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hklo hlog0.le
    nlinarith only [hh, Real.log_two_gt_d9, hB0]
  have hhigh : ((2^k : ℕ) : ℝ) ≤ Real.exp ((14 / 5 : ℝ) * B) := by
    rw [nat_two_pow_exp]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hkhi hlog0.le
    nlinarith only [hh, Real.log_two_lt_d9, hB0]
  refine ⟨hlow, ?_⟩
  calc
    (4 * T * (2^k : ℕ) : ℝ) ≤
        Real.exp ((1 / 10 : ℝ) * B) * Real.exp ((1 / 10 : ℝ) * B) * Real.exp ((14 / 5 : ℝ) * B) := by
      gcongr
    _ = Real.exp (3 * (B : ℝ)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp ((16 / 5 : ℝ) * B) := Real.exp_le_exp.mpr (by linarith only [hB0])

theorem amplificationCoefficientPairs_size :
    ∀ᶠ B : ℕ in atTop, ∀ T a c : ℕ, 0 < T →
      (T : ℝ) ≤ Real.exp ((1 / 10 : ℝ) * B) →
      (a, c) ∈ amplificationCoefficientPairs B T →
      (a : ℝ) ≤ Real.exp ((16 / 5 : ℝ) * B) ∧
        (c : ℝ) ≤ Real.exp ((16 / 5 : ℝ) * B) := by
  classical
  filter_upwards [coefficientDyadicBox_scales] with B hs
  intro T a c hT hTsize hac
  obtain ⟨k, hk, hbox⟩ := mem_biUnion.mp (mem_filter.mp hac).1
  have hscale := (hs T k hTsize hk).2
  obtain ⟨ha, hc⟩ := mem_product.mp hbox
  have ha' : (a : ℝ) ≤ 4 * T * (2^k : ℕ) := by exact_mod_cast (mem_Ico.mp ha).2.le
  have hc' : (c : ℝ) ≤ 2 * (2^k : ℕ) := by exact_mod_cast (mem_Ico.mp hc).2.le
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  refine ⟨ha'.trans hscale, hc'.trans (le_trans ?_ hscale)⟩
  have hh := mul_le_mul_of_nonneg_right hT1 (by positivity : (0 : ℝ) ≤ (2^k : ℕ))
  nlinarith only [hh, show (0 : ℝ) ≤ (2^k : ℕ) by positivity]

end JointDickman

end OAI
