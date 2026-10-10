import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSieveMonotone

namespace OAI

/-! # Removing a fixed divisor from the actual quadratic coefficient array -/

namespace Ostmann

open scoped Classical BigOperators

 theorem mem_oddSquarefreeRange_mul {s r N : ℕ} (hs : Squarefree s) (ho : Odd s) :
    s * r ∈ oddSquarefreeRange N ↔
      r ∈ oddSquarefreeRange (N / s) ∧ s.Coprime r := by
  have hs0 : 0 < s := Nat.pos_of_ne_zero hs.ne_zero
  constructor
  · intro h
    obtain ⟨hrange, hodd, hsq⟩ := Finset.mem_filter.mp h
    obtain ⟨hcop, _, hrsq⟩ := Nat.squarefree_mul_iff.mp hsq
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero hrsq.ne_zero,
      (Nat.le_div_iff_mul_le hs0).mpr ?_⟩, hodd.of_dvd_nat (dvd_mul_left r s), hrsq⟩, hcop⟩
    simpa only [Nat.mul_comm] using (Finset.mem_Icc.mp hrange).2
  · rintro ⟨hr, hcop⟩
    obtain ⟨hrange, hodd, hsq⟩ := Finset.mem_filter.mp hr
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨Nat.mul_pos hs0 (Finset.mem_Icc.mp hrange).1, ?_⟩,
      ho.mul hodd, (Nat.squarefree_mul hcop).mpr ⟨hs, hsq⟩⟩
    simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hs0).mp (Finset.mem_Icc.mp hrange).2

 theorem sum_oddSquarefree_multiples {R : Type*} [AddCommMonoid R]
    (s N : ℕ) (hs : Squarefree s) (ho : Odd s) (f : ℕ → R) :
    (∑ n ∈ (oddSquarefreeRange N).filter (fun n => s ∣ n), f n) =
      ∑ r ∈ (oddSquarefreeRange (N / s)).filter (fun r => s.Coprime r), f (s * r) := by
  symm
  apply Finset.sum_bij (fun r _ => s * r)
  · intro r hr
    exact Finset.mem_filter.mpr
      ⟨(mem_oddSquarefreeRange_mul hs ho).mpr (Finset.mem_filter.mp hr), dvd_mul_right s r⟩
  · intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hs.ne_zero) hab
  · intro n hn
    obtain ⟨hn, hd⟩ := Finset.mem_filter.mp hn
    have he : s * (n / s) = n := Nat.mul_div_cancel' hd
    refine ⟨n / s, ?_, he⟩
    apply Finset.mem_filter.mpr
    exact (mem_oddSquarefreeRange_mul hs ho).mp (he.symm ▸ hn)
  · intro _ _
    rfl

noncomputable def quadraticDivisibilityCoeff (s : ℕ) (b : ℕ → ℂ) (r : ℕ) : ℂ :=
  if s.Coprime r then b (s * r) else 0

 theorem quadraticTransposeSum_divisibility (s N : ℕ) (hs : Squarefree s) (ho : Odd s)
    (b : ℕ → ℂ) (m : ℤ) :
    quadraticTransposeSum N (fun n => if s ∣ n then b n else 0) m =
      (jacobiSym m s : ℂ) * quadraticTransposeSum (N / s) (quadraticDivisibilityCoeff s b) m := by
  unfold quadraticTransposeSum
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter, sum_oddSquarefree_multiples s N hs ho]
  simp only [quadraticDivisibilityCoeff, ite_mul, zero_mul, ← Finset.sum_filter]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hr0 := (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2.2.ne_zero
  rw [jacobiSym.mul_right' m hs.ne_zero hr0]
  push_cast
  ring

 theorem quadraticSieveEnergy_divisibility (s N : ℕ) (hs : Squarefree s) (ho : Odd s)
    (b : ℕ → ℂ) :
    quadraticSieveEnergy (N / s) (quadraticDivisibilityCoeff s b) =
      quadraticSieveEnergy N (fun n => if s ∣ n then b n else 0) := by
  unfold quadraticSieveEnergy quadraticDivisibilityCoeff
  simp only [apply_ite, norm_zero, ite_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, ← Finset.sum_filter]
  exact (sum_oddSquarefree_multiples s N hs ho (fun n => ‖b n‖ ^ 2)).symm

 theorem quadratic_divisibility_energy {s M N : ℕ} {K : ℝ}
    (hs : Squarefree s) (ho : Odd s) (h : QuadraticSieveBound M (N / s) K)
    (b : ℕ → ℂ) :
    (∑ m ∈ oddSquarefreeRange M,
      ‖quadraticTransposeSum N (fun n => if s ∣ n then b n else 0) m‖ ^ 2) ≤
      2 * K * quadraticSieveEnergy N (fun n => if s ∣ n then b n else 0) := by
  have hb := quadraticTranspose_of_bound h (quadraticDivisibilityCoeff s b)
  rw [quadraticSieveEnergy_divisibility s N hs ho] at hb
  apply le_trans _ hb
  apply Finset.sum_le_sum
  intro m _
  rw [quadraticTransposeSum_divisibility s N hs ho, norm_mul, mul_pow]
  rcases jacobiSym.trichotomy (m : ℤ) s with hm | hm | hm <;> simp [hm]

end Ostmann

end OAI
