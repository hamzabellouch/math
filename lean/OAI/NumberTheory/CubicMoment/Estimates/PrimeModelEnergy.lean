import OAI.NumberTheory.CubicMoment.Estimates.PrimeSharpCutoff
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace OAI

/-! The model coefficient energy on a full initial prime segment.
The elementary integral test keeps the small primes in the actual sum. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma sum_neg_third_le (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (n:ℝ)^(-1/3:ℝ)) ≤ (3/2:ℝ)*(N:ℝ)^(2/3:ℝ) := by
  have ha : AntitoneOn (fun x : ℝ => x^(-1/3:ℝ)) (Set.Ioc 0 (0+(N:ℝ))) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos hx.1 hxy (by norm_num)
  have hi : IntegrableOn (fun x : ℝ => x^(-1/3:ℝ)) (Set.Icc 0 (0+(N:ℝ))) := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by positivity)).mp
    exact intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hb := ha.sum_le_integral_of_integrableOn hi
  have he : (∑ n ∈ Finset.Icc 1 N, (n:ℝ)^(-1/3:ℝ)) =
      ∑ i ∈ Finset.range N, ((i+1:ℕ):ℝ)^(-1/3:ℝ) := by
    clear ha hi hb
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]
  rw [he]
  rw [integral_rpow (r := (-1/3:ℝ)) (Or.inl (by norm_num))] at hb
  simp only [zero_add, show (-1/3:ℝ)+1 = 2/3 by norm_num,
    Real.zero_rpow (by norm_num : (2/3:ℝ) ≠ 0), sub_zero] at hb
  convert hb using 1
  ring

lemma prime_initial_segment_neg_third (P : Finset Eisenstein) (N : ℕ)
    (hP : ∀ p ∈ P, primaryPrime p ∧ normNat p ≤ N) :
    (∑ p ∈ P, norm p^(-1/3:ℝ)) ≤ 3*(N:ℝ)^(2/3:ℝ) := by
  have hi : ∀ p ∈ P, normNat p ∈ Finset.Icc 1 N := by
    intro p hp
    exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr
      (normNat_ne_zero (hP p hp).1.2.ne_zero), (hP p hp).2⟩
  have hf (n : ℕ) : ((P.filter (fun p => normNat p = n)).card:ℝ) ≤ 2 := by
    have hh := prime_norm_fiber_card_le_two P (fun p hp => (hP p hp).1) (n:ℤ)
    have he : (P.filter (fun p => (normNat p:ℤ) = (n:ℤ))) =
        P.filter (fun p => normNat p = n) := by ext; simp
    rw [he] at hh
    exact_mod_cast hh
  calc
    _ = ∑ n ∈ Finset.Icc 1 N,
        ((P.filter (fun p => normNat p = n)).card:ℝ)*(n:ℝ)^(-1/3:ℝ) := by
      rw [← Finset.sum_fiberwise_of_maps_to hi]
      apply Finset.sum_congr rfl
      intro n hn
      have he (p : Eisenstein) (hp : p ∈ P.filter (fun p => normNat p = n)) :
          norm p^(-1/3:ℝ) = (n:ℝ)^(-1/3:ℝ) := by
        rw [← normNat_cast, (Finset.mem_filter.mp hp).2]
      simp_rw [Finset.sum_congr rfl he]
      simp
    _ ≤ ∑ n ∈ Finset.Icc 1 N, 2*(n:ℝ)^(-1/3:ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_right (hf n) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = 2*∑ n ∈ Finset.Icc 1 N, (n:ℝ)^(-1/3:ℝ) := by rw [Finset.mul_sum]
    _ ≤ 3*(N:ℝ)^(2/3:ℝ) := by linarith [sum_neg_third_le N]

lemma prime_model_initial_segment_energy (P : Finset Eisenstein) (c : Eisenstein → ℂ)
    {X M : ℝ} (hX : 0 < X) (_hM : 0 ≤ M)
    (hP : ∀ p ∈ P, primaryPrime p ∧ norm p ≤ 4*X)
    (hc : ∀ p ∈ P, ‖c p‖ ≤ M) :
    (∑ p ∈ P, ‖c p*((norm p^(-1/6:ℝ):ℝ):ℂ)‖^2) ≤
      36*M^2*X^(2/3:ℝ) := by
  let N := ⌊4*X⌋₊
  have hN : (N:ℝ) ≤ 4*X := Nat.floor_le (by positivity)
  have hn : ∀ p ∈ P, primaryPrime p ∧ normNat p ≤ N := by
    intro p hp
    refine ⟨(hP p hp).1,Nat.le_floor ?_⟩
    simpa only [normNat_cast] using (hP p hp).2
  have he (p : Eisenstein) (hp : p ∈ P) :
      ‖c p*((norm p^(-1/6:ℝ):ℝ):ℂ)‖^2 ≤ M^2*norm p^(-1/3:ℝ) := by
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg p) _)]
    have hpow : (norm p^(-1/6:ℝ))^2 = norm p^(-1/3:ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg p)]
      norm_num
    rw [hpow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (_root_.norm_nonneg _) (hc p hp) 2)
      (Real.rpow_nonneg (norm_nonneg p) _)
  have hfour : (4:ℝ)^(2/3:ℝ) ≤ 4 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1:ℝ) ≤ 4) (by norm_num : (2/3:ℝ) ≤ 1)
  calc
    _ ≤ M^2*∑ p ∈ P, norm p^(-1/3:ℝ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum he
    _ ≤ M^2*(3*(N:ℝ)^(2/3:ℝ)) :=
      mul_le_mul_of_nonneg_left (prime_initial_segment_neg_third P N hn) (sq_nonneg _)
    _ ≤ M^2*(3*(4*X)^(2/3:ℝ)) := by gcongr
    _ ≤ 36*M^2*X^(2/3:ℝ) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hX.le]
      have hz : 0 ≤ M^2*X^(2/3:ℝ) := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hfour
        hz]

end CubicFirstMoment

end

end OAI
