import OAI.NumberTheory.JointDickman.Probability.TwoSplitLaw
import Mathlib.Data.ZMod.Basic

namespace OAI

/-! # The exact two-hit law at one prime for consecutive integers -/

namespace JointDickman
open Finset

noncomputable def consecutivePrimeHit {p : ℕ} (r : ZMod p) : Bool × Bool :=
  (decide (r = 0), decide (r = -1))

noncomputable def consecutiveHitMass (q : ℝ) (v : Bool × Bool) : ℝ :=
  if v.1 then (if v.2 then 0 else q) else (if v.2 then q else 1 - 2*q)

noncomputable def independentHitMass (q : ℝ) (v : Bool × Bool) : ℝ :=
  bernoulliBitMass q v.1 * bernoulliBitMass q v.2

open Classical in
theorem consecutivePrimeHit_fiber {p : ℕ} (hp : p.Prime) (v : Bool × Bool) :
    let : NeZero p := ⟨hp.ne_zero⟩
    (∑ r : ZMod p, if consecutivePrimeHit r = v then (1 / (p : ℝ)) else 0) =
      consecutiveHitMass (1 / (p : ℝ)) v := by
  let : NeZero p := ⟨hp.ne_zero⟩
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hne : (0 : ZMod p) ≠ -1 := by
    intro h
    have : (1 : ZMod p) = 0 := by simpa using congrArg Neg.neg h.symm
    exact hp.ne_one (ZMod.one_eq_zero_iff.mp this)
  rcases v with ⟨b,c⟩
  cases b <;> cases c
  · have he (r : ZMod p) :
        (if consecutivePrimeHit r = (false, false) then (1 / (p : ℝ)) else 0) =
          (1 / (p : ℝ)) - (if r = 0 then (1 / (p : ℝ)) else 0) -
            (if r = -1 then (1 / (p : ℝ)) else 0) := by
      by_cases h0 : r = 0 <;> by_cases h1 : r = -1
      · exact False.elim (hne (h0.symm.trans h1))
      all_goals simp [consecutivePrimeHit, h0, h1, hne, Ne.symm hne]
    simp_rw [he]
    simp only [sum_sub_distrib, sum_const, card_univ, ZMod.card, nsmul_eq_mul,
      sum_ite_eq', mem_univ, ite_true, consecutiveHitMass, Bool.false_eq_true, ite_false]
    field_simp
    ring
  · have he (r : ZMod p) :
        (if consecutivePrimeHit r = (false, true) then (1 / (p : ℝ)) else 0) =
          if r = -1 then (1 / (p : ℝ)) else 0 := by
      by_cases h0 : r = 0 <;> by_cases h1 : r = -1
      · exact False.elim (hne (h0.symm.trans h1))
      all_goals simp [consecutivePrimeHit, h0, h1, hne, Ne.symm hne]
    simp_rw [he]
    simp [consecutiveHitMass]
  · have he (r : ZMod p) :
        (if consecutivePrimeHit r = (true, false) then (1 / (p : ℝ)) else 0) =
          if r = 0 then (1 / (p : ℝ)) else 0 := by
      by_cases h0 : r = 0 <;> by_cases h1 : r = -1
      · exact False.elim (hne (h0.symm.trans h1))
      all_goals simp [consecutivePrimeHit, h0, h1, hne, Ne.symm hne]
    simp_rw [he]
    simp [consecutiveHitMass]
  · have he (r : ZMod p) :
        (if consecutivePrimeHit r = (true, true) then (1 / (p : ℝ)) else 0) = 0 := by
      by_cases h0 : r = 0 <;> by_cases h1 : r = -1
      · exact False.elim (hne (h0.symm.trans h1))
      all_goals simp [consecutivePrimeHit, h0, h1, hne, Ne.symm hne]
    simp_rw [he]
    simp [consecutiveHitMass]

theorem consecutiveHitMass_nonneg {q : ℝ} (hq : 0 ≤ q) (h2 : 2*q ≤ 1)
    (v : Bool × Bool) : 0 ≤ consecutiveHitMass q v := by
  rcases v with ⟨b,c⟩
  cases b <;> cases c <;> simp only [consecutiveHitMass, Bool.false_eq_true,
    ite_false, ite_true] <;> linarith

theorem consecutiveHitMass_sum (q : ℝ) : ∑ v, consecutiveHitMass q v = 1 := by
  simp [Fintype.sum_prod_type, consecutiveHitMass]
  ring

theorem independentHitMass_sum (q : ℝ) : ∑ v, independentHitMass q v = 1 := by
  simp [Fintype.sum_prod_type, independentHitMass, bernoulliBitMass]
  ring

theorem consecutiveHitMass_l1 (q : ℝ) :
    (∑ v, |consecutiveHitMass q v - independentHitMass q v|) = 4*q^2 := by
  have hneg : 1 - 2*q - (1-q)*(1-q) = -q^2 := by ring
  have hpos : q - (1-q)*q = q^2 := by ring
  have hpos' : q - q*(1-q) = q^2 := by ring
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, consecutiveHitMass,
    independentHitMass, bernoulliBitMass, Bool.false_eq_true, ite_false, ite_true,
    zero_sub, abs_neg, hneg, hpos, hpos', abs_of_nonneg (sq_nonneg q)]
  simp only [← pow_two, abs_of_nonneg (sq_nonneg q)]
  ring

end JointDickman

end OAI
