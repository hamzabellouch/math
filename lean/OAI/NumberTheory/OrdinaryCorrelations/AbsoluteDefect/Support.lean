import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.TupleProduct

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

namespace OrdinaryDirichletMixedMoments
open OrdinaryDirichletMeanSquare OrdinaryPrimeDirichletMoments Finset MeasureTheory

def support (A B : Finset ℕ) : Finset ℕ := (A ×ˢ B).image (fun z => z.1*z.2)

def coefficient (A B : Finset ℕ) (a b : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ z ∈ A ×ˢ B, if z.1*z.2=n then a z.1*b z.2 else 0

lemma multiplication_injOn (A B : Finset ℕ)
    (hA : ∀ n ∈ A, 0 < n) (hc : ∀ n ∈ A, ∀ m ∈ B, Nat.Coprime n m) :
    Set.InjOn (fun z : ℕ × ℕ => z.1*z.2) ↑(A ×ˢ B : Finset (ℕ × ℕ)) := by
  rintro ⟨n,m⟩ hnm ⟨n',m'⟩ hnm' he
  change n*m=n'*m' at he
  obtain ⟨hn,hm⟩ := mem_product.mp hnm
  obtain ⟨hn',hm'⟩ := mem_product.mp hnm'
  have hnn' : n ∣ n' := (hc n hn m' hm').dvd_of_dvd_mul_right
    (he ▸ dvd_mul_right n m)
  have hn'n : n' ∣ n := (hc n' hn' m hm).dvd_of_dvd_mul_right
    (he.symm ▸ dvd_mul_right n' m')
  have hne := Nat.dvd_antisymm hnn' hn'n
  subst n'
  have hme : m=m' := Nat.eq_of_mul_eq_mul_left (hA n hn) he
  subst m'
  rfl

lemma coefficient_at_mul (A B : Finset ℕ) (a b : ℕ → ℂ)
    (hi : Set.InjOn (fun z : ℕ × ℕ => z.1*z.2) ↑(A ×ˢ B : Finset (ℕ × ℕ)))
    {n m : ℕ} (hn : n ∈ A) (hm : m ∈ B) :
    coefficient A B a b (n*m) = a n*b m := by
  classical
  have hnm : (n,m) ∈ A ×ˢ B := mem_product.mpr ⟨hn,hm⟩
  unfold coefficient
  rw [sum_eq_single (n,m)]
  · simp
  · intro z hz hznot
    have hne : z.1*z.2 ≠ n*m := fun h => hznot (hi hz hnm h)
    simp [hne]
  · intro hnnot
    exact False.elim (hnnot hnm)

lemma phase_log_mul {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (t : ℝ) :
    phase (Real.log (n*m : ℕ)) t = phase (Real.log n) t * phase (Real.log m) t := by
  rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hn.ne') (by exact_mod_cast hm.ne')]
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma polynomial_mul (A B : Finset ℕ) (a b : ℕ → ℂ)
    (hA : ∀ n ∈ A, 0 < n) (hB : ∀ m ∈ B, 0 < m)
    (hi : Set.InjOn (fun z : ℕ × ℕ => z.1*z.2) ↑(A ×ˢ B : Finset (ℕ × ℕ))) (t : ℝ) :
    polynomial (support A B) (coefficient A B a b) (fun n => Real.log n) t =
      polynomial A a (fun n => Real.log n) t *
      polynomial B b (fun n => Real.log n) t := by
  classical
  unfold polynomial support
  rw [sum_image hi, sum_product, Finset.sum_mul]
  apply sum_congr rfl
  intro n hn
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro m hm
  rw [coefficient_at_mul A B a b hi hn hm, phase_log_mul (hA n hn) (hB m hm)]
  ring

lemma coefficient_energy (A B : Finset ℕ) (a b : ℕ → ℂ)
    (hi : Set.InjOn (fun z : ℕ × ℕ => z.1*z.2) ↑(A ×ˢ B : Finset (ℕ × ℕ))) :
    ∑ n ∈ support A B, ‖coefficient A B a b n‖^2 =
      (∑ n ∈ A, ‖a n‖^2) * (∑ m ∈ B, ‖b m‖^2) := by
  classical
  unfold support
  rw [sum_image hi, sum_product, Finset.sum_mul]
  apply sum_congr rfl
  intro n hn
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro m hm
  rw [coefficient_at_mul A B a b hi hn hm, norm_mul, mul_pow]

theorem coprime_mixed_moment (A B : Finset ℕ) (a b : ℕ → ℂ) {N M T : ℝ}
    (hN : 0 < N) (hM : 0 < M) (hT : 0 < T)
    (hA : ∀ n ∈ A, 0 < (n:ℝ) ∧ (n:ℝ) ≤ N)
    (hB : ∀ m ∈ B, 0 < (m:ℝ) ∧ (m:ℝ) ≤ M)
    (hc : ∀ n ∈ A, ∀ m ∈ B, Nat.Coprime n m) :
    (∫ t : ℝ in Set.Icc (-T) T,
      ‖polynomial A a (fun n => Real.log n) t‖^2 *
      ‖polynomial B b (fun n => Real.log n) t‖^2) ≤
      4 * Real.exp (1+1/4) * gaussianConstant * (T+N*M) *
        (∑ n ∈ A, ‖a n‖^2) * (∑ m ∈ B, ‖b m‖^2) := by
  have hAn : ∀ n ∈ A, 0 < n := fun n hn => by exact_mod_cast (hA n hn).1
  have hBn : ∀ m ∈ B, 0 < m := fun m hm => by exact_mod_cast (hB m hm).1
  have hi := multiplication_injOn A B hAn hc
  have hs : ∀ k ∈ support A B, 0 < (k:ℝ) ∧ (k:ℝ) ≤ N*M := by
    intro k hk
    obtain ⟨⟨n,m⟩, hnm, rfl⟩ := mem_image.mp hk
    obtain ⟨hn,hm⟩ := mem_product.mp hnm
    rw [Nat.cast_mul]
    exact ⟨mul_pos (hA n hn).1 (hB m hm).1,
      mul_le_mul (hA n hn).2 (hB m hm).2 (hB m hm).1.le hN.le⟩
  have he (t : ℝ) :
      ‖polynomial A a (fun n => Real.log n) t‖^2 *
      ‖polynomial B b (fun n => Real.log n) t‖^2 =
      ‖polynomial (support A B) (coefficient A B a b) (fun n => Real.log n) t‖^2 := by
    rw [polynomial_mul A B a b hAn hBn hi t, norm_mul, mul_pow]
  simp_rw [he]
  have h := logarithmic_interval_energy (support A B) (coefficient A B a b)
    (mul_pos hN hM) hT hs
  rw [coefficient_energy A B a b hi] at h
  simpa only [mul_assoc] using h

end OrdinaryDirichletMixedMoments

end

end OAI
