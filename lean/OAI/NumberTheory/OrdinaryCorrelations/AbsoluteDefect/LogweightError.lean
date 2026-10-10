import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set

namespace OrdinaryLogWeightRemoval

lemma logweight_error (b : ℕ → ℂ) {X R : ℝ} (hX : 1≤X) (hR : 1≤R)
    (hb : ∀n∈Finset.Icc 1 ⌊X⌋₊, ‖b n‖≤1) :
    ‖(Real.log X:ℂ)*(∑n∈Finset.Icc 1 ⌊X⌋₊, b n)-
      (∑n∈Finset.Icc 1 ⌊X⌋₊, (Real.log (n:ℝ):ℂ)*b n)‖ ≤
        (X/R)*Real.log X+X*Real.log R := by
  have hx : 0<X := lt_of_lt_of_le zero_lt_one hX
  have hr : 0<R := lt_of_lt_of_le zero_lt_one hR
  have hlx : 0≤Real.log X := Real.log_nonneg hX
  have hlr : 0≤Real.log R := Real.log_nonneg hR
  let S : Finset ℕ := Finset.Icc 1 ⌊X⌋₊
  let A : Finset ℕ := S.filter (fun n => n≤⌊X/R⌋₊)
  have hpoint (n : ℕ) (hn : n∈S) :
      ‖((Real.log X:ℂ)-(Real.log (n:ℝ):ℂ))*b n‖ ≤
        (if n≤⌊X/R⌋₊ then Real.log X else 0)+Real.log R := by
    have hn1 : 1≤n := (Finset.mem_Icc.mp hn).1
    have hnr : 0<(n:ℝ) := by exact_mod_cast hn1
    have hnX : (n:ℝ)≤X := (Nat.le_floor_iff hx.le).1 (Finset.mem_Icc.mp hn).2
    have hlogn : 0≤Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
    have hlogXn : Real.log (n:ℝ)≤Real.log X := Real.log_le_log hnr hnX
    have hdiff : 0≤Real.log X-Real.log (n:ℝ) := sub_nonneg.mpr hlogXn
    rw [norm_mul,←Complex.ofReal_sub,Complex.norm_real,Real.norm_of_nonneg hdiff]
    apply (mul_le_mul_of_nonneg_left (hb n hn) hdiff).trans
    rw [mul_one]
    by_cases hsmall : n≤⌊X/R⌋₊
    · rw [ite_eq_left hsmall]
      linarith
    · rw [ite_eq_right hsmall,zero_add]
      have hXn : X/R<(n:ℝ) := by
        exact lt_of_not_ge (fun hh => hsmall ((Nat.le_floor_iff (div_pos hx hr).le).2 hh))
      have hprod : X≤(n:ℝ)*R := (le_of_lt ((div_lt_iff₀ hr).1 hXn))
      have hh := Real.log_le_log hx hprod
      rw [Real.log_mul hnr.ne' hr.ne'] at hh
      linarith
  have hA : A⊆Finset.Icc 1 ⌊X/R⌋₊ := by
    intro n hn
    obtain ⟨hn,hn'⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,hn'⟩
  have hAc : (A.card:ℝ)≤X/R := by
    have hh : A.card≤⌊X/R⌋₊ := by simpa using Finset.card_le_card hA
    exact (by exact_mod_cast hh : (A.card:ℝ)≤(⌊X/R⌋₊:ℝ)).trans (Nat.floor_le (div_pos hx hr).le)
  have hSc : (S.card:ℝ)≤X := by
    simpa only [S,Nat.card_Icc,Nat.add_sub_cancel,Nat.cast_id] using Nat.floor_le hx.le
  have he : (Real.log X:ℂ)*(∑n∈S,b n)-(∑n∈S,(Real.log (n:ℝ):ℂ)*b n)=
      ∑n∈S,((Real.log X:ℂ)-(Real.log (n:ℝ):ℂ))*b n := by
    rw [Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  rw [he]
  calc
    ‖∑n∈S,((Real.log X:ℂ)-(Real.log (n:ℝ):ℂ))*b n‖ ≤
      ∑n∈S,‖((Real.log X:ℂ)-(Real.log (n:ℝ):ℂ))*b n‖ := norm_sum_le _ _
    _ ≤ ∑n∈S,((if n≤⌊X/R⌋₊ then Real.log X else 0)+Real.log R) :=
      Finset.sum_le_sum hpoint
    _ = (A.card:ℝ)*Real.log X+(S.card:ℝ)*Real.log R := by
      rw [Finset.sum_add_distrib,←Finset.sum_filter]
      simp [A]
    _ ≤ (X/R)*Real.log X+X*Real.log R :=
      add_le_add (mul_le_mul_of_nonneg_right hAc hlx) (mul_le_mul_of_nonneg_right hSc hlr)

end OrdinaryLogWeightRemoval

end

end OAI
