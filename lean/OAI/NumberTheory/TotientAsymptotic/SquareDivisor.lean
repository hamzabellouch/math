import OAI.NumberTheory.TotientAsymptotic.PublishedComparison

namespace OAI

/-! A square in a finite product comes from one factor or two distinct factors. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma prime_dvd_product {ι : Type*} (I : Finset ι) (f : ι → ℕ)
    {q : ℕ} (hq : q.Prime) (hd : q ∣ ∏ j ∈ I, f j) : ∃ j ∈ I, q ∣ f j := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using hq.not_dvd_one hd
  | @insert a I ha ih =>
    rw [Finset.prod_insert ha] at hd
    rcases hq.dvd_mul.mp hd with h | h
    · exact ⟨a,Finset.mem_insert_self _ _,h⟩
    · obtain ⟨j,hj,hdj⟩ := ih h
      exact ⟨j,Finset.mem_insert_of_mem hj,hdj⟩

lemma square_dvd_product {ι : Type*} (I : Finset ι) (f : ι → ℕ)
    {q : ℕ} (hq : q.Prime) (hd : q^2 ∣ ∏ j ∈ I, f j) :
    (∃ j ∈ I, q^2 ∣ f j) ∨
    (∃ j ∈ I, ∃ k ∈ I, j ≠ k ∧ q ∣ f j ∧ q ∣ f k) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    have hh : q ∣ 1 := (dvd_pow_self q (by norm_num : 2 ≠ 0)).trans (by simpa using hd)
    exact (hq.not_dvd_one hh).elim
  | @insert a I ha ih =>
    rw [Finset.prod_insert ha] at hd
    by_cases h1 : q^2 ∣ f a
    · exact Or.inl ⟨a,Finset.mem_insert_self _ _,h1⟩
    by_cases h2 : q^2 ∣ ∏ j ∈ I, f j
    · rcases ih h2 with ⟨j,hj,hj2⟩ | ⟨j,hj,k,hk,hjk,hqj,hqk⟩
      · exact Or.inl ⟨j,Finset.mem_insert_of_mem hj,hj2⟩
      · exact Or.inr ⟨j,Finset.mem_insert_of_mem hj,k,Finset.mem_insert_of_mem hk,hjk,hqj,hqk⟩
    · have haq : q ∣ f a := by
        by_contra hn
        exact h2 (hq.prime.pow_dvd_of_dvd_mul_left 2 hn hd)
      have hIq : q ∣ ∏ j ∈ I, f j := by
        by_contra hn
        exact h1 (hq.prime.pow_dvd_of_dvd_mul_right 2 hn hd)
      obtain ⟨k,hk,hqk⟩ := prime_dvd_product I f hq hIq
      exact Or.inr ⟨a,Finset.mem_insert_self _ _,k,Finset.mem_insert_of_mem hk,
        (fun he => ha (he ▸ hk)),haq,hqk⟩

end TotientAsymptotic

end

end OAI
