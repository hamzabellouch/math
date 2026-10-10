import OAI.NumberTheory.TwoPoint.Bounds.PrimeDefectMajorant
import OAI.NumberTheory.TwoPoint.Bounds.FiniteAverages

namespace OAI

/-! Exact one-prime p² averages of the elementary modulus majorant. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma sum_zero_multiples_of_dvd (a N : ℕ) (haN : a ∣ N) :
    (∑ v ∈ range N, if a ∣ v then (1 : ℝ) else 0) = (N / a : ℕ) := by
  let F : ℕ → ℝ := fun v => if a ∣ v then 1 else 0
  have hpos : (∑ v ∈ range N, F (v + 1)) = (N / a : ℕ) := by
    have hh := congrArg (fun n : ℕ => (n : ℝ)) (Nat.card_multiples N a)
    simpa only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using hh
  have h1 := sum_range_succ F N
  have h2 := sum_range_succ' F N
  have hF0 : F 0 = 1 := by simp [F]
  have hFN : F N = 1 := by simp [F, haN]
  change (∑ v ∈ range N, F v) = _
  linarith

lemma primeDefectLocal_sum (f : ℕ → ℂ) {p : ℕ} (hp : p.Prime) :
    (∑ n ∈ range (p ^ 2), primeDefectLocal f p n) =
      (p : ℝ) ^ 2 - (1 - ‖f p‖) * ((p : ℝ) - 1) := by
  simp_rw [primeDefectLocal_formula]
  rw [sum_sub_distrib, ← mul_sum, sum_sub_distrib,
    sum_zero_multiples_of_dvd p (p ^ 2) (by simp [pow_two]),
    sum_zero_multiples_of_dvd (p ^ 2) (p ^ 2) (dvd_refl _)]
  have hpp : p ^ 2 / p = p := by rw [pow_two, Nat.mul_div_cancel_left _ hp.pos]
  rw [hpp, Nat.div_self (pow_pos hp.pos 2)]
  simp

lemma primeDefectLocal_average (f : ℕ → ℂ) {p : ℕ} [NeZero (p ^ 2)] (hp : p.Prime) :
    uniformAverage (fun r : ZMod (p ^ 2) => primeDefectLocal f p r.val) =
      1 - (1 - ‖f p‖) * (1 / (p : ℝ) - 1 / (p : ℝ) ^ 2) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  let e : Fin (p ^ 2) ≃ ZMod (p ^ 2) :=
    { toFun := fun i => (i.val : ZMod (p ^ 2))
      invFun := fun r => ⟨r.val, r.val_lt⟩
      left_inv := fun i => Fin.ext (ZMod.val_natCast_of_lt i.isLt)
      right_inv := fun r => ZMod.natCast_zmod_val r }
  have hsum : (∑ r : ZMod (p ^ 2), primeDefectLocal f p r.val) =
      ∑ n ∈ range (p ^ 2), primeDefectLocal f p n := by
    rw [← e.sum_comp (fun r => primeDefectLocal f p r.val)]
    rw [← Fin.sum_univ_eq_sum_range]
    apply sum_congr rfl
    intro i _
    exact congrArg (primeDefectLocal f p) (ZMod.val_natCast_of_lt i.isLt)
  unfold uniformAverage
  rw [hsum, ZMod.card, primeDefectLocal_sum f hp, Nat.cast_pow]
  field_simp [hp0]

end TwoPointCorrelations

end OAI
