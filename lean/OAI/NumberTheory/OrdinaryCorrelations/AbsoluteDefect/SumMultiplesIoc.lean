import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.BilinearPart
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Poly

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
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset

namespace OrdinaryCorrelations

namespace SourcePrimeFactor
open Finset
theorem sum_multiples_Ioc (v u p : ℕ) (hp : 0 < p) (g : ℕ → ℂ) :
    (∑ n ∈ (Finset.Ioc v u).filter (fun n => p ∣ n), g n) =
      ∑ m ∈ Ioc (v / p) (u / p), g (p * m) := by
  symm
  refine sum_bij (fun m _ => p * m) ?_ ?_ ?_ ?_
  · intro m hm
    rcases mem_Ioc.mp hm with ⟨hl, hu⟩
    apply mem_filter.mpr
    refine ⟨mem_Ioc.mpr ⟨?_, ?_⟩, dvd_mul_right p m⟩
    · simpa only [mul_comm] using (Nat.div_lt_iff_lt_mul hp).mp hl
    · simpa only [mul_comm] using (Nat.le_div_iff_mul_le hp).mp hu
  · intro m hm m' hm' he
    exact Nat.eq_of_mul_eq_mul_left hp he
  · intro n hn
    rcases mem_filter.mp hn with ⟨hn, hpn⟩
    have he := Nat.mul_div_cancel' hpn
    refine ⟨n / p, mem_Ioc.mpr ⟨?_, ?_⟩, he⟩
    · apply (Nat.div_lt_iff_lt_mul hp).mpr
      simpa only [mul_comm (n / p), he] using (mem_Ioc.mp hn).1
    · apply (Nat.le_div_iff_mul_le hp).mpr
      simpa only [mul_comm (n / p), he] using (mem_Ioc.mp hn).2
  · intro m hm
    rfl

def roughPart (P : Finset ℕ) (f g : ℕ → ℂ) (v D : ℕ) : ℂ :=
  ∑ n ∈ (Finset.Ioc v (v + D)).filter (fun n => primeCount P n = 0), f n * g n

def bilinearPart (P : Finset ℕ) (f g : ℕ → ℂ) (v D : ℕ) : ℂ :=
  ∑ p ∈ P, f p * ∑ m ∈ (Finset.Ioc (v / p) ((v + D) / p)).filter (fun m => ¬p ∣ m),
    (f m * g (p * m)) / ((primeCount P m : ℂ) + 1)

def diagonalPart (P : Finset ℕ) (f g : ℕ → ℂ) (v D : ℕ) : ℂ :=
  ∑ p ∈ P, ∑ m ∈ (Finset.Ioc (v / p) ((v + D) / p)).filter (fun m => p ∣ m),
    (f (p * m) * g (p * m)) / (primeCount P (p * m) : ℂ)

theorem short_sum_decomposition (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (f g : ℕ → ℂ) (hf : Multiplicative f) (v D : ℕ) :
    (∑ n ∈ Ioc v (v + D), f n * g n) =
      roughPart P f g v D + bilinearPart P f g v D + diagonalPart P f g v D := by
  classical
  have hsplit : (∑ n ∈ Ioc v (v + D), f n * g n) =
      roughPart P f g v D + ∑ p ∈ P, ∑ m ∈ Ioc (v / p) ((v + D) / p),
        f (p * m) * g (p * m) / (primeCount P (p * m) : ℂ) := by
    calc
      _ = ∑ n ∈ Ioc v (v + D), ((if primeCount P n = 0 then f n * g n else 0) +
          ∑ p ∈ P, if p ∣ n then (f n * g n) / (primeCount P n : ℂ) else 0) :=
        sum_congr rfl (fun n _ => weighted_partition P n (f n * g n))
      _ = roughPart P f g v D + ∑ p ∈ P, ∑ n ∈ (Finset.Ioc v (v + D)).filter
          (fun n => p ∣ n), (f n * g n) / (primeCount P n : ℂ) := by
        rw [sum_add_distrib, sum_comm]
        simp only [roughPart, sum_filter]
      _ = _ := by
        congr 1
        apply sum_congr rfl
        intro p hp
        exact sum_multiples_Ioc v (v + D) p (hP p hp).pos _
  rw [hsplit, add_assoc]
  congr 1
  unfold bilinearPart diagonalPart
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro p hp
  rw [mul_sum]
  have hm : ∀ m ∈ Finset.Ioc (v / p) ((v + D) / p), ¬p ∣ m →
      f (p * m) * g (p * m) / (primeCount P (p * m) : ℂ) =
        f p * ((f m * g (p * m)) / ((primeCount P m : ℂ) + 1)) := by
    intro m hm hpm
    have hm0 : 0 < m := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hm).1
    rw [hf p m (hP p hp).pos hm0 ((hP p hp).coprime_iff_not_dvd.mpr hpm),
      primeCount_mul hP hp hpm, Nat.cast_add, Nat.cast_one]
    ring
  calc
    _ = (∑ m ∈ (Finset.Ioc (v / p) ((v + D) / p)).filter (fun m => ¬p ∣ m),
          f (p * m) * g (p * m) / (primeCount P (p * m) : ℂ)) +
        ∑ m ∈ (Finset.Ioc (v / p) ((v + D) / p)).filter (fun m => p ∣ m),
          f (p * m) * g (p * m) / (primeCount P (p * m) : ℂ) := by
      simpa only [not_not] using
        (sum_filter_add_sum_filter_not (Ioc (v / p) ((v + D) / p)) (fun m => ¬p ∣ m)
          (fun m => f (p * m) * g (p * m) / (primeCount P (p * m) : ℂ))).symm
    _ = _ := by
      congr 1
      apply sum_congr rfl
      intro m hm'
      exact hm m (mem_filter.mp hm').1 (mem_filter.mp hm').2

theorem norm_roughPart_le (P : Finset ℕ) (f g : ℕ → ℂ) (v D : ℕ)
    (hf : OneBounded f) (hg : OneBounded g) :
    ‖roughPart P f g v D‖ ≤
      ((Finset.Ioc v (v + D)).filter (fun n => primeCount P n = 0)).card := by
  unfold roughPart
  calc
    _ ≤ ∑ n ∈ (Finset.Ioc v (v + D)).filter (fun n => primeCount P n = 0), ‖f n * g n‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _n ∈ (Finset.Ioc v (v + D)).filter (fun n => primeCount P n = 0), (1 : ℝ) := by
      apply sum_le_sum
      intro n hn
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hf n)).trans (hg n)
    _ = _ := by simp

theorem norm_diagonalPart_le (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (f g : ℕ → ℂ) (v D : ℕ) (hf : OneBounded f) (hg : OneBounded g) :
    ‖diagonalPart P f g v D‖ ≤
      ∑ p ∈ P, (((v + D) / (p * p) - v / (p * p) : ℕ) : ℝ) := by
  unfold diagonalPart
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro p hp
  rw [sum_multiples_Ioc (v / p) ((v + D) / p) p (hP p hp).pos,
    Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
  calc
    _ ≤ ∑ m ∈ Ioc (v / (p * p)) ((v + D) / (p * p)),
        ‖f (p * (p * m)) * g (p * (p * m)) / (primeCount P (p * (p * m)) : ℂ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _m ∈ Ioc (v / (p * p)) ((v + D) / (p * p)), (1 : ℝ) := by
      apply sum_le_sum
      intro m hm
      rw [norm_div, norm_mul, Complex.norm_natCast]
      have hc : (1 : ℝ) ≤ primeCount P (p * (p * m)) := by
        exact_mod_cast primeCount_pos hp (dvd_mul_right p (p * m))
      apply (div_le_one (by linarith)).mpr
      exact ((mul_le_of_le_one_left (norm_nonneg _) (hf _)).trans (hg _)).trans hc
    _ = _ := by simp only [sum_const, nsmul_eq_mul, mul_one, Nat.card_Ioc]

theorem count_multiples_le (v D q : ℕ) :
    (((v + D) / q - v / q : ℕ) : ℝ) ≤ (D : ℝ) / q + 1 := by
  have hq : ((v + D) / q - v / q : ℕ) ≤ (D / q + 1 : ℕ) := by
    apply Nat.sub_le_iff_le_add.mpr
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Nat.add_div_le_div_add_div_add_one v D q
  calc
    _ ≤ ((D / q + 1 : ℕ) : ℝ) := by exact_mod_cast hq
    _ = ((D / q : ℕ) : ℝ) + (1 : ℝ) := by push_cast; rfl
    _ ≤ _ := add_le_add (Nat.cast_div_le (α := ℝ) (m := D) (n := q)) le_rfl

theorem norm_diagonalPart_le_reciprocal (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (f g : ℕ → ℂ) (v D : ℕ)
    (hf : OneBounded f) (hg : OneBounded g) :
    ‖diagonalPart P f g v D‖ ≤ (D : ℝ) * (∑ p ∈ P, 1 / (p : ℝ)^2) + P.card := by
  apply (norm_diagonalPart_le P hP f g v D hf hg).trans
  calc
    _ ≤ ∑ p ∈ P, ((D : ℝ) / (p * p : ℕ) + 1) :=
      sum_le_sum (fun p _ => count_multiples_le v D (p * p))
    _ = _ := by
      simp only [sum_add_distrib, sum_const, nsmul_eq_mul, mul_one, mul_sum,
        Nat.cast_mul, div_eq_mul_inv, one_mul, pow_two]

end SourcePrimeFactor
end OrdinaryCorrelations

end

end OAI
