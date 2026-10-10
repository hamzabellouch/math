import OAI.NumberTheory.Ostmann.QuadraticSieveDualCorrelationsTransform
import OAI.NumberTheory.Ostmann.QuadraticSieveRootGaussMellinScale

namespace OAI

namespace Ostmann.QuadraticSieve
open ComplexConjugate

theorem complementaryPair_divisor_exchange (S : Finset ℕ) (a : ℕ → ℂ) (N : ℕ)
    (F : ℕ → ℕ → ℂ) (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N) :
    complementaryPair S a (fun q => ∑ d ∈ q.divisors, F d q) =
      ∑ d ∈ Finset.Icc 1 (N^2), ∑ n ∈ S, ∑ t ∈ S,
        if Nat.Coprime n t ∧ d ∣ n*t then a n * conj (a t) * F d (n*t) else 0 := by
  classical
  have hterm (n : ℕ) (hn : n ∈ S) (t : ℕ) (ht : t ∈ S) :
      (if Nat.Coprime n t then a n * conj (a t) * (∑ d ∈ (n*t).divisors, F d (n*t)) else 0) =
        ∑ d ∈ Finset.Icc 1 (N^2), if Nat.Coprime n t ∧ d ∣ n*t then
          a n * conj (a t) * F d (n*t) else 0 := by
    rw [divisor_sum_eq_Icc (n*t) (N^2) (Nat.mul_pos (hS n hn).1 (hS t ht).1)
      (by simpa only [pow_two] using Nat.mul_le_mul (hS n hn).2 (hS t ht).2)]
    by_cases hc : Nat.Coprime n t
    · rw [ite_eq_left hc, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hdq : d ∣ n*t
      · rw [ite_eq_left hdq, ite_eq_left (show Nat.Coprime n t ∧ d ∣ n*t from ⟨hc,hdq⟩)]
      · rw [ite_eq_right hdq, ite_eq_right (show ¬ (Nat.Coprime n t ∧ d ∣ n*t) from fun h => hdq h.2), mul_zero]
    · simp [hc]
  unfold complementaryPair
  rw [Finset.sum_congr rfl (fun n hn => Finset.sum_congr rfl (fun t ht => hterm n hn t ht))]
  rw [Finset.sum_congr rfl (fun n hn => Finset.sum_comm), Finset.sum_comm]

theorem gaussPair_divisor_exchange (S : Finset ℕ) (a : ℕ → ℂ) (N v : ℕ) (c : ℤ)
    (F : ℕ → ℂ) (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N) :
    complementaryPair S a (fun q => jacobiGaussRatio q * (jacobiSym (c*(v : ℤ)) q : ℂ) *
      (∑ d ∈ q.divisors, F d)) =
      ∑ d ∈ Finset.Icc 1 (N^2), F d *
        gaussProductDivisorJacobiRow S S a (fun n => conj (a n)) c d (v : ℤ) := by
  simp_rw [Finset.mul_sum]
  rw [complementaryPair_divisor_exchange S a N _ hS]
  simp only [gaussProductDivisorJacobiRow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro t ht
  split_ifs <;> ring

theorem rootGaussPair_divisor_exchange (S : Finset ℕ) (a : ℕ → ℂ) (N v : ℕ) (c : ℤ)
    (F : ℕ → ℕ → ℂ) (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N) :
    complementaryPair S a (fun q => (Real.sqrt (q : ℝ) : ℂ) * jacobiGaussRatio q *
      (jacobiSym (c*(v : ℤ)) q : ℂ) * (∑ d ∈ q.divisors, F d q)) =
      ∑ d ∈ Finset.Icc 1 (N^2), ∑ n ∈ S, ∑ t ∈ S,
        rootGaussMellinKernel a (fun n => conj (a n)) c d v n t * F d (n*t) := by
  simp_rw [Finset.mul_sum]
  rw [complementaryPair_divisor_exchange S a N _ hS]
  simp only [rootGaussMellinKernel, Nat.cast_mul]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro t ht
  split_ifs <;> ring

theorem sum_rootGaussMellinKernel (S : Finset ℕ) (a : ℕ → ℂ) (c : ℤ) (d v : ℕ) :
    (∑ n ∈ S, ∑ t ∈ S, rootGaussMellinKernel a (fun n => conj (a n)) c d v n t) =
      gaussProductDivisorJacobiRow S S (sqrtCoefficients a)
        (sqrtCoefficients (fun n => conj (a n))) c d (v : ℤ) := by
  simp only [rootGaussMellinKernel_eq, gaussMellinKernel, gaussProductDivisorJacobiRow]

theorem dual_correction_root_scale {M e b q : ℝ} (hM : 0 < M) (he : 0 < e)
    (hb : 0 < b) (hq : 0 ≤ q) :
    (M/e)*Real.sqrt (e*q/(M*b)) = Real.sqrt (M/(e*b))*Real.sqrt q := by
  rw [Real.sqrt_div (mul_nonneg he.le hq), Real.sqrt_mul he.le, Real.sqrt_mul hM.le,
    Real.sqrt_div hM.le, Real.sqrt_mul he.le]
  have he0 := (Real.sqrt_pos.mpr he).ne'
  have hM0 := (Real.sqrt_pos.mpr hM).ne'
  have hb0 := (Real.sqrt_pos.mpr hb).ne'
  field_simp
  ring_nf
  simp only [Real.sq_sqrt he.le, Real.sq_sqrt hM.le]
  ring

theorem dual_correction_fourier_scale {M e b q : ℝ} (hM : 0 < M) (he : 0 < e)
    (_hb : 0 < b) (hq : 0 ≤ q) (l d : ℝ) :
    l*(Real.sqrt (e*q/(M*b))/d) =
      (l*Real.sqrt (e/M))*Real.sqrt q/(d*Real.sqrt b) := by
  rw [show e*q/(M*b) = (e/M)*q/b by ring,
    Real.sqrt_div (mul_nonneg (div_nonneg he.le hM.le) hq),
    Real.sqrt_mul (div_nonneg he.le hM.le)]
  ring

end Ostmann.QuadraticSieve

end OAI
