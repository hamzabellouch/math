import OAI.NumberTheory.Ostmann.QuadraticSieveGcdSeparation
import OAI.NumberTheory.Ostmann.QuadraticSieveNorm

namespace OAI

namespace Ostmann.QuadraticSieve

def quotientSupport (S : Finset ℕ) (d : ℕ) : Finset ℕ :=
  (S.filter (fun n => d ∣ n)).image (fun n => n / d)

@[simp] theorem mem_quotientSupport {S : Finset ℕ} {d r : ℕ} :
    r ∈ quotientSupport S d ↔ ∃ n ∈ S, d ∣ n ∧ n / d = r := by
  simp only [quotientSupport, Finset.mem_image, Finset.mem_filter, and_assoc]

theorem sum_quotientSupport {R : Type*} [AddCommMonoid R]
    (S : Finset ℕ) (d : ℕ) (f : ℕ → R) :
    (∑ r ∈ quotientSupport S d, f (d * r)) =
      ∑ n ∈ S, if d ∣ n then f n else 0 := by
  unfold quotientSupport
  rw [Finset.sum_image]
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hd : d ∣ n
    · simp [hd, Nat.mul_div_cancel' hd]
    · simp [hd]
  · intro n hn t ht hnt
    change n / d = t / d at hnt
    have hdn := (Finset.mem_filter.mp hn).2
    have hdt := (Finset.mem_filter.mp ht).2
    calc
      n = d * (n / d) := (Nat.mul_div_cancel' hdn).symm
      _ = d * (t / d) := by rw [hnt]
      _ = t := Nat.mul_div_cancel' hdt

theorem quotientSupport_pos {S : Finset ℕ} {d r : ℕ}
    (hS : ∀ n ∈ S, 0 < n) (hr : r ∈ quotientSupport S d) : 0 < r := by
  obtain ⟨n, hn, hdn, rfl⟩ := mem_quotientSupport.mp hr
  apply Nat.pos_of_ne_zero
  intro hzero
  have heq := Nat.mul_div_cancel' hdn
  rw [hzero, mul_zero] at heq
  exact (hS n hn).ne' heq.symm

theorem quotientSupport_odd {S : Finset ℕ} {d r : ℕ}
    (hS : ∀ n ∈ S, Odd n) (hr : r ∈ quotientSupport S d) : Odd r := by
  obtain ⟨n, hn, hdn, rfl⟩ := mem_quotientSupport.mp hr
  exact Nat.coprime_two_left.mp
    ((hS n hn).coprime_two_left.of_dvd_right (Nat.div_dvd_of_dvd hdn))

theorem quotientSupport_subset_oddSquarefreeUpTo {S : Finset ℕ} {U d : ℕ}
    (hS : S ⊆ oddSquarefreeUpTo U) :
    quotientSupport S d ⊆ oddSquarefreeUpTo (U / d) := by
  intro r hr
  have hrpos := quotientSupport_pos (fun n hn => (mem_oddSquarefreeUpTo.mp (hS hn)).1) hr
  have hrodd := quotientSupport_odd (fun n hn => (mem_oddSquarefreeUpTo.mp (hS hn)).2.2.1) hr
  obtain ⟨n, hn, hdn, rfl⟩ := mem_quotientSupport.mp hr
  obtain ⟨hn1, hnU, hno, hnsq⟩ := mem_oddSquarefreeUpTo.mp (hS hn)
  exact mem_oddSquarefreeUpTo.mpr ⟨hrpos, Nat.div_le_div_right hnU, hrodd,
    hnsq.squarefree_of_dvd (Nat.div_dvd_of_dvd hdn)⟩

def quotientCoefficients (d k : ℕ) (a : ℕ → ℂ) (r : ℕ) : ℂ :=
  if k ∣ d * r then a (d * r) else 0

theorem sum_divisor_jacobi_eq_quotient (S : Finset ℕ) (a : ℕ → ℂ)
    (m : ℤ) (d k : ℕ) [NeZero d] (hS : ∀ n ∈ S, 0 < n) :
    (∑ n ∈ S, if d ∣ n ∧ k ∣ n then a n * (jacobiSym m n : ℂ) else 0) =
      (jacobiSym m d : ℂ) * ∑ r ∈ quotientSupport S d,
        quotientCoefficients d k a r * (jacobiSym m r : ℂ) := by
  calc
    _ = ∑ r ∈ quotientSupport S d,
        if k ∣ d * r then a (d * r) * (jacobiSym m (d * r) : ℂ) else 0 := by
      simpa only [ite_and] using
        (sum_quotientSupport S d (fun n => if k ∣ n then a n * (jacobiSym m n : ℂ) else 0)).symm
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      rw [jacobiSym.mul_right' m (NeZero.ne d) (quotientSupport_pos hS hr).ne', Int.cast_mul]
      by_cases hk : k ∣ d * r <;>
        simp [quotientCoefficients, hk, mul_left_comm, mul_comm]

theorem norm_sq_divisor_jacobi_le_quotient (S : Finset ℕ) (a : ℕ → ℂ)
    (m : ℤ) (d k : ℕ) [NeZero d] (hS : ∀ n ∈ S, 0 < n) :
    ‖∑ n ∈ S, if d ∣ n ∧ k ∣ n then a n * (jacobiSym m n : ℂ) else 0‖ ^ 2 ≤
      ‖∑ r ∈ quotientSupport S d, quotientCoefficients d k a r * (jacobiSym m r : ℂ)‖ ^ 2 := by
  rw [sum_divisor_jacobi_eq_quotient S a m d k hS]
  rcases jacobiSym.trichotomy m d with h | h | h <;> simp [h]

theorem divisor_jacobi_energy_le_quotient_norm (V S : Finset ℕ) (a : ℕ → ℂ)
    (d k : ℕ) [NeZero d] (hV : ∀ v ∈ V, Odd v)
    (hS : ∀ n ∈ S, 0 < n ∧ Odd n) :
    (∑ v ∈ V, ‖∑ n ∈ S, if d ∣ n ∧ k ∣ n then a n * (jacobiSym (v : ℤ) n : ℂ) else 0‖ ^ 2) ≤
      2 * quadraticNorm V (quotientSupport S d) *
        coefficientEnergy (quotientSupport S d) (quotientCoefficients d k a) := by
  calc
    _ ≤ numeratorEnergy 1 V (quotientSupport S d) (quotientCoefficients d k a) := by
      apply Finset.sum_le_sum
      intro v hv
      simpa only [one_mul] using
        norm_sq_divisor_jacobi_le_quotient S a (v : ℤ) d k (fun n hn => (hS n hn).1)
    _ ≤ _ := numeratorEnergy_le_of_unsigned V (quotientSupport S d) (quotientCoefficients d k a) 1
      hV (fun r hr => quotientSupport_odd (fun n hn => (hS n hn).2) hr)
      (quadraticNorm_nonneg V (quotientSupport S d))
      (jacobiEnergy_le_quadraticNorm V (quotientSupport S d))

theorem coefficientEnergy_quotientCoefficients (S : Finset ℕ) (a : ℕ → ℂ) (d k : ℕ) :
    coefficientEnergy (quotientSupport S d) (quotientCoefficients d k a) =
      ∑ n ∈ S, if d ∣ n ∧ k ∣ n then ‖a n‖ ^ 2 else 0 := by
  unfold coefficientEnergy quotientCoefficients
  calc
    _ = ∑ r ∈ quotientSupport S d,
        if k ∣ d * r then ‖a (d * r)‖ ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro r hr
      split <;> simp
    _ = _ := by
      simpa only [ite_and] using
        sum_quotientSupport S d (fun n => if k ∣ n then ‖a n‖ ^ 2 else 0)

noncomputable def divisorWeightedEnergy (S : Finset ℕ) (d : ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑ n ∈ S, (n.divisors.card : ℝ) * ‖if d ∣ n then a n else 0‖ ^ 2

theorem divisorWeightedEnergy_nonneg (S : Finset ℕ) (d : ℕ) (a : ℕ → ℂ) :
    0 ≤ divisorWeightedEnergy S d a :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))

theorem sum_coefficientEnergy_quotient (S : Finset ℕ) (a : ℕ → ℂ) (d N : ℕ)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N) :
    (∑ k ∈ Finset.Icc 1 N,
      coefficientEnergy (quotientSupport S d) (quotientCoefficients d k a)) =
      divisorWeightedEnergy S d a := by
  simp_rw [coefficientEnergy_quotientCoefficients]
  calc
    _ = ∑ k ∈ Finset.Icc 1 N, ∑ n ∈ S,
        if k ∣ n then ‖if d ∣ n then a n else 0‖ ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hd : d ∣ n <;> by_cases hk : k ∣ n <;> simp [hd, hk]
    _ = _ := sum_divisor_restricted_norm_sq S (fun n => if d ∣ n then a n else 0) N hS

theorem sum_divisor_jacobi_energy_le_quotient_norm (V S : Finset ℕ) (a : ℕ → ℂ)
    (d N : ℕ) [NeZero d] (hV : ∀ v ∈ V, Odd v)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N ∧ Odd n) :
    (∑ v ∈ V, ∑ k ∈ Finset.Icc 1 N,
      ‖∑ n ∈ S, if d ∣ n ∧ k ∣ n then a n * (jacobiSym (v : ℤ) n : ℂ) else 0‖ ^ 2) ≤
      2 * quadraticNorm V (quotientSupport S d) * divisorWeightedEnergy S d a := by
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 N, 2 * quadraticNorm V (quotientSupport S d) *
        coefficientEnergy (quotientSupport S d) (quotientCoefficients d k a) := by
      apply Finset.sum_le_sum
      intro k hk
      exact divisor_jacobi_energy_le_quotient_norm V S a d k hV
        (fun n hn => ⟨(hS n hn).1, (hS n hn).2.2⟩)
    _ = _ := by
      rw [← Finset.mul_sum,
        sum_coefficientEnergy_quotient S a d N (fun n hn => ⟨(hS n hn).1, (hS n hn).2.1⟩)]

end Ostmann.QuadraticSieve

end OAI
