import OAI.NumberTheory.JointDickman.Amplification.FiniteProductTail
import OAI.NumberTheory.JointDickman.Probability.SingularSeriesMoments

namespace OAI

/-! # A mean approximation of the totient ratio by finitely many prime factors -/
namespace JointDickman
open Finset Classical

noncomputable def totientLocalProduct (Y n : ℕ) : ℝ :=
  ∏ p ∈ Nat.primesLE Y, if p ∣ n then 1+1/((p : ℝ)-1) else 1

theorem prime_totient_increment_bound {p : ℕ} (hp : p.Prime) :
    0 ≤ 1/((p : ℝ)-1) / p ∧ 1/((p : ℝ)-1) / p ≤ 2/(p : ℝ)^2 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : 0 < (p : ℝ)-1 := by linarith
  constructor
  · positivity
  · rw [div_le_iff₀ hp0,div_le_iff₀ hp1]
    field_simp
    nlinarith

theorem prime_totient_increment_sum (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (∑ p ∈ P, 1/((p : ℝ)-1)/p) ≤ 2 := by
  calc
    _ ≤ ∑ p ∈ P, 2/(p : ℝ)^2 :=
      sum_le_sum (fun p hp => (prime_totient_increment_bound (hP p hp)).2)
    _ = 2*∑ p ∈ P, 1/(p : ℝ)^2 := by rw [mul_sum]; congr 1; ext; ring
    _ ≤ 2*1 := mul_le_mul_of_nonneg_left
      (by
        simpa using (sum_reciprocal_square_tail P (show (1 : ℕ) ≠ 0 by omega)
          (fun p hp => (hP p hp).one_lt))) (by norm_num)
    _ = 2 := by ring

theorem prime_totient_increment_tail {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {Y : ℕ} (hY : 0 < Y) (hPY : ∀ p ∈ P, Y < p) :
    (∑ p ∈ P, 1/((p : ℝ)-1)/p) ≤ 2/(Y : ℝ) := by
  calc
    _ ≤ ∑ p ∈ P, 2/(p : ℝ)^2 :=
      sum_le_sum (fun p hp => (prime_totient_increment_bound (hP p hp)).2)
    _ = 2*∑ p ∈ P, 1/(p : ℝ)^2 := by rw [mul_sum]; congr 1; ext; ring
    _ ≤ 2*(1/(Y : ℝ)) := mul_le_mul_of_nonneg_left
      (sum_reciprocal_square_tail P (Nat.ne_of_gt hY) hPY) (by norm_num)
    _ = _ := by ring

theorem totientLocalProduct_eq_ratio {n Y : ℕ} (hn : 0 < n) (hnY : n ≤ Y) :
    totientLocalProduct Y n = (n : ℝ)/n.totient := by
  have hfac : n.primeFactors = (Nat.primesLE Y).filter (fun p => p ∣ n) := by
    ext p
    simp only [mem_filter,Nat.mem_primesLE,Nat.mem_primeFactors]
    constructor
    · rintro ⟨hp,hd,_⟩
      exact ⟨⟨(Nat.le_of_dvd hn hd).trans hnY,hp⟩,hd⟩
    · rintro ⟨⟨_,hp⟩,hd⟩
      exact ⟨hp,hd,Nat.ne_of_gt hn⟩
  have he : (n : ℝ)/n.totient = ∏ p ∈ n.primeFactors, (1-1/(p : ℝ))⁻¹ := by
    rw [totient_eq_prime_product_real,prod_inv_distrib]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    field_simp
  rw [he,totientLocalProduct,← prod_filter,← hfac]
  apply prod_congr rfl
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hp1 : (p : ℝ)-1 ≠ 0 := by linarith
  field_simp
  ring

theorem totientLocalProduct_mono {Y Z : ℕ} (hYZ : Y ≤ Z) (n : ℕ) :
    totientLocalProduct Y n ≤ totientLocalProduct Z n := by
  unfold totientLocalProduct
  apply prod_le_prod_of_subset_of_one_le₀
  · intro p hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hp).1.trans hYZ,
      (Nat.mem_primesLE.mp hp).2⟩
  · intro p hp
    split_ifs
    · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
      exact add_nonneg zero_le_one (div_nonneg zero_le_one (by linarith))
    · norm_num
  · intro p hp _
    split_ifs
    · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
      have : 0 ≤ 1/((p : ℝ)-1) := div_nonneg zero_le_one (by linarith)
      linarith
    · exact le_rfl

theorem totientLocalProduct_mean_error (Y U : ℕ) (hY : 0 < Y) :
    (∑ n ∈ Ioc 0 U, |(n : ℝ)/n.totient-totientLocalProduct Y n|) ≤
      (2*Real.exp 2)*(U : ℝ)/Y := by
  let P := Nat.primesLE (max U Y)
  let Q := Nat.primesLE Y
  have hQP : Q ⊆ P := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hp).1.trans (le_max_right _ _),
      (Nat.mem_primesLE.mp hp).2⟩
  have hP p (hp : p ∈ P) := (Nat.mem_primesLE.mp hp).2
  have hb p (hp : p ∈ P) : 0 ≤ 1/((p : ℝ)-1) := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    exact div_nonneg zero_le_one (by linarith)
  have hs : (∑ n ∈ Ioc 0 U, |(n : ℝ)/n.totient-totientLocalProduct Y n|) =
      ∑ n ∈ Ioc 0 U, ((∏ p ∈ P, if p ∣ n then 1+1/((p : ℝ)-1) else 1)-
        ∏ p ∈ Q, if p ∣ n then 1+1/((p : ℝ)-1) else 1) := by
    apply sum_congr rfl
    intro n hn
    have he := totientLocalProduct_eq_ratio (mem_Ioc.mp hn).1
      ((mem_Ioc.mp hn).2.trans (le_max_left U Y))
    rw [← he,abs_of_nonneg (sub_nonneg.mpr (totientLocalProduct_mono (le_max_right U Y) n))]
    rfl
  rw [hs]
  have hdiff := (prod_one_add_difference_bound hQP
    (fun p : ℕ => 1/((p : ℝ)-1)/p)
    (fun p hp => (prime_totient_increment_bound (hP p hp)).1)).2
  have htail := prime_totient_increment_tail
    (fun p (hp : p ∈ P \ Q) => hP p (mem_sdiff.mp hp).1) hY (by
      intro p hp
      have hpp := hP p (mem_sdiff.mp hp).1
      have hn := (mem_sdiff.mp hp).2
      simp only [Q,Nat.mem_primesLE,not_and] at hn
      exact Nat.lt_of_not_ge (fun h => hn h hpp))
  have hsum := prime_totient_increment_sum P hP
  calc
    _ ≤ (U : ℝ)*((∏ p ∈ P, (1+(1/((p : ℝ)-1))/p))-
        ∏ p ∈ Q, (1+(1/((p : ℝ)-1))/p)) :=
      divisor_product_difference_mean hQP hP (fun p => 1/((p : ℝ)-1)) hb U
    _ ≤ (U : ℝ)*(Real.exp 2*(2/(Y : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg U)
      exact hdiff.trans (mul_le_mul (Real.exp_le_exp.mpr hsum) htail
        (sum_nonneg (fun p hp => (prime_totient_increment_bound (hP p (mem_sdiff.mp hp).1)).1))
        (Real.exp_pos 2).le)
    _ = _ := by ring

end JointDickman

end OAI
