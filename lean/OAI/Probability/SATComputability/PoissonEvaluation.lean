import OAI.Probability.SATComputability.PoissonKilling
import OAI.Probability.SATComputability.ArithmeticConstructors
import OAI.Probability.SATComputability.EffectiveSums

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal Topology
local instance poissonEvaluationRatPrimcodable : Primcodable ℚ := PeriodicLattice.RecursiveArithmetic.ratPrimcodable

theorem nat_succ_le_two_pow_real (k : ℕ) : (k : ℝ)+1 ≤ (2 : ℝ)^k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [Nat.cast_succ, pow_succ]
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    nlinarith

theorem poisson_linear_integrable (r : ℝ≥0) (f : ℕ → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ k, |f k| ≤ C*((k : ℝ)+1)) :
    Integrable f (poissonMeasure r) := by
  apply Integrable.mono' ((poisson_power_integrable r (by norm_num : (0 : ℝ) ≤ 2)).const_mul C)
    (measurable_of_countable _).aestronglyMeasurable
  filter_upwards [] with k
  rw [Real.norm_eq_abs]
  exact (hf k).trans (mul_le_mul_of_nonneg_left (nat_succ_le_two_pow_real k) hC)

theorem poisson_linear_tail (r : ℝ≥0) (f : ℕ → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ k, |f k| ≤ C*((k : ℝ)+1)) (L : ℕ) :
    |(∫ k, f k ∂poissonMeasure r) -
      ∑ k ∈ Finset.range L, (Real.exp (-(r : ℝ))*(r : ℝ)^k/k.factorial)*f k| ≤
      C*Real.exp (3*(r : ℝ))/(2 : ℝ)^L := by
  let low : ℕ → ℝ := fun k => if k < L then f k else 0
  let high : ℕ → ℝ := fun k => if k < L then 0 else f k
  have hl : Integrable low (poissonMeasure r) :=
    poisson_linear_integrable r low hC (fun k => by
      dsimp only [low]
      split_ifs
      · exact hf k
      · simpa using mul_nonneg hC (by positivity : (0 : ℝ) ≤ (k : ℝ)+1))
  have hh : Integrable high (poissonMeasure r) :=
    poisson_linear_integrable r high hC (fun k => by
      dsimp only [high]
      split_ifs
      · simpa using mul_nonneg hC (by positivity : (0 : ℝ) ≤ (k : ℝ)+1)
      · exact hf k)
  have he : ∫ k, low k ∂poissonMeasure r =
      ∑ k ∈ Finset.range L, (Real.exp (-(r : ℝ))*(r : ℝ)^k/k.factorial)*f k := by
    rw [integral_poissonMeasure]
    rw [tsum_eq_sum (s := Finset.range L)]
    · apply Finset.sum_congr rfl
      intro k hk
      simp only [smul_eq_mul, low, ite_eq_left (Finset.mem_range.mp hk)]
    · intro k hk
      simp only [low, Finset.mem_range, not_lt] at hk ⊢
      simp [Nat.not_lt.mpr hk]
  have hs : f = fun k => low k + high k := by
    funext k
    dsimp [low, high]
    split_ifs <;> simp
  rw [← he, hs, integral_add hl hh, add_sub_cancel_left]
  apply (abs_integral_le_integral_abs).trans
  calc
    _ ≤ ∫ k : ℕ, C*(4 : ℝ)^k/(2 : ℝ)^L ∂poissonMeasure r := by
      apply integral_mono hh.abs
        (((poisson_power_integrable r (by norm_num : (0 : ℝ) ≤ 4)).const_mul C).div_const _)
      intro k
      dsimp only [high]
      split_ifs with hk
      · simp only [abs_zero]
        positivity
      · apply (hf k).trans
        apply (mul_le_mul_of_nonneg_left (nat_succ_le_two_pow_real k) hC).trans
        apply (le_div_iff₀ (by positivity)).mpr
        have hp : (2 : ℝ)^L ≤ (2 : ℝ)^k :=
          pow_le_pow_right₀ (by norm_num) (Nat.le_of_not_gt hk)
        calc
          C*2^k*2^L ≤ C*2^k*2^k := mul_le_mul_of_nonneg_left hp (by positivity)
          _ = C*4^k := by rw [mul_assoc, ← mul_pow]; norm_num
    _ = _ := by
      rw [integral_div, integral_const_mul, poisson_power_integral r (by norm_num : (0 : ℝ) ≤ 4)]
      congr 2
      norm_num
      ring

@[fun_prop] theorem factorial_computable : Computable Nat.factorial := by
  have h := Computable.nat_rec (f := fun n : ℕ => n) (g := fun _ => (1 : ℕ))
    (h := fun _ p => (p.1+1)*p.2) Computable.id (Computable.const 1)
    (by unfold Computable₂; fun_prop)
  exact h.of_eq (fun n => by induction n <;> simp_all [Nat.factorial_succ])

theorem exp_le_three_natCeil (q : ℚ) :
    Real.exp (q : ℝ) ≤ (3 : ℝ)^⌈q⌉₊ := by
  have hceil : (q : ℝ) ≤ (⌈q⌉₊ : ℕ) := by exact_mod_cast (Nat.le_ceil q)
  calc
    _ ≤ Real.exp (⌈q⌉₊ : ℕ) := Real.exp_le_exp.mpr hceil
    _ = (Real.exp 1)^⌈q⌉₊ := by rw [← Real.exp_nat_mul]; simp
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le _

theorem effective_poisson_expectation {A : Type} [Primcodable A]
    (rate : A → ℚ) (hrate : Computable rate) (hnonneg : ∀ a, 0 ≤ rate a)
    (C : A → ℕ) (hC : Computable C) (f : A → ℕ → ℝ)
    (hf : PeriodicLattice.CertifiedReal.Effective (fun p : A × ℕ => f p.1 p.2))
    (hbound : ∀ a k, |f a k| ≤ (C a : ℝ)*((k : ℝ)+1)) :
    PeriodicLattice.CertifiedReal.Effective (fun a =>
      ∫ k, f a k ∂poissonMeasure ⟨rate a, by exact_mod_cast hnonneg a⟩) := by
  let rateNN : A → ℝ≥0 := fun a => ⟨rate a, by exact_mod_cast hnonneg a⟩
  let g : A → ℕ → ℝ := fun a L =>
    ∑ k ∈ Finset.range L, (Real.exp (-(rate a : ℝ))*(rate a : ℝ)^k/k.factorial)*f a k
  have ht : PeriodicLattice.CertifiedReal.Effective (fun p : A × ℕ =>
      (Real.exp (-(rate p.1 : ℝ))*(rate p.1 : ℝ)^p.2/p.2.factorial)*f p.1 p.2) := by
    have he := (PeriodicLattice.CertifiedReal.rational
      (show Computable (fun p : A × ℕ => -rate p.1) by fun_prop)).exp
    have hr := PeriodicLattice.CertifiedReal.rational
      (show Computable (fun p : A × ℕ => (rate p.1)^p.2/(p.2.factorial : ℚ)) by fun_prop)
    convert (he.mul hr).mul hf using 1
    funext p
    push_cast
    ring
  have hg : PeriodicLattice.CertifiedReal.Effective (fun p : A × ℕ => g p.1 p.2) := by
    apply PeriodicLattice.CertifiedReal.Effective.sum_range (m := Prod.snd)
    · exact ht.comp (show Computable (fun p : (A × ℕ) × ℕ => (p.1.1,p.2)) by fun_prop)
    · exact Computable.snd
  let tail : A × ℕ → ℚ := fun p => (C p.1 : ℚ)*3^⌈3*rate p.1⌉₊/2^p.2
  apply PeriodicLattice.CertifiedReal.effective_limit hg tail
  · dsimp only [tail]
    fun_prop
  · intro a L
    have h := poisson_linear_tail (rateNN a) (f a) (Nat.cast_nonneg (C a)) (hbound a) L
    apply h.trans
    have hExp := exp_le_three_natCeil (3*rate a)
    change (C a : ℝ) * Real.exp (3*(rateNN a : ℝ))/(2 : ℝ)^L ≤ (tail (a,L) : ℝ)
    dsimp only [tail, rateNN]
    push_cast at hExp ⊢
    gcongr
    exact hExp
  · intro a
    dsimp only [tail]
    push_cast
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num : (2 : ℝ)⁻¹ < 1)).const_mul
        ((C a : ℝ)*3^⌈3*rate a⌉₊)
    simpa only [div_eq_mul_inv, inv_pow, mul_zero] using h

end FixedClauseThreshold.Computability

end OAI
