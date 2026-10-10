import OAI.Combinatorics.PolynomialVacuum.Algebra.InterpolationDefinitions

namespace OAI

namespace PolynomialVacuumInterpolation
open Polynomial

 

theorem integral_interpolation {R ι : Type*} [CommRing R] [IsDomain R] [DecompositionMonoid R]
    (s : Finset ι) (a v : ι → R)
    (hrel : ∀ i ∈ s, ∀ j ∈ s, ∀ k ∈ s, i ≠ j → i ≠ k → j ≠ k →
      IsRelPrime (a i-a j) (a i-a k))
    (hcompat : ∀ i ∈ s, ∀ j ∈ s, a i-a j ∣ v i-v j) :
    ∃ p : R[X], p.degree < (s.card : WithBot ℕ) ∧ ∀ i ∈ s, p.eval (a i)=v i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨0,by simp,by simp⟩
  | @insert b s hb ih =>
    obtain ⟨p,hdeg,heval⟩ := ih
      (fun i hi j hj k hk hij hik hjk => hrel i (by simp [hi]) j (by simp [hj])
        k (by simp [hk]) hij hik hjk)
      (fun i hi j hj => hcompat i (by simp [hi]) j (by simp [hj]))
    have hdvd : (∏ i ∈ s, (a b-a i)) ∣ v b-p.eval (a b) := by
      apply Finset.prod_dvd_of_isRelPrime
      · intro i hi j hj hij
        exact hrel b (Finset.mem_insert_self b s) i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)
          (by rintro rfl; exact hb hi) (by rintro rfl; exact hb hj) hij
      · intro i hi
        have h1 := hcompat b (by simp) i (by simp [hi])
        have h2 := Polynomial.sub_dvd_eval_sub (a b) (a i) p
        have hh : v b-p.eval (a b) = (v b-v i)-(p.eval (a b)-p.eval (a i)) := by
          rw [heval i hi]; ring
        rw [hh]
        exact dvd_sub h1 h2
    obtain ⟨c,hc⟩ := hdvd
    let q : R[X] := ∏ i ∈ s, (X-C (a i))
    have hqeval (r : R) : q.eval r = ∏ i ∈ s, (r-a i) := by
      simp [q,Polynomial.eval_prod]
    have hqzero (i : ι) (hi : i ∈ s) : q.eval (a i)=0 := by
      rw [hqeval]
      exact Finset.prod_eq_zero hi (sub_self _)
    have hqdeg : q.degree ≤ (s.card : WithBot ℕ) := by
      calc q.degree ≤ ∑ i ∈ s, (X-C (a i) : R[X]).degree := Polynomial.degree_prod_le s _
           _ = (s.card : WithBot ℕ) := by simp
    refine ⟨p+C c*q,?_,?_⟩
    · rw [Finset.card_insert_of_notMem hb]
      apply lt_of_le_of_lt (Polynomial.degree_add_le p (C c*q))
      apply max_lt
      · exact lt_trans hdeg (by exact_mod_cast Nat.lt_succ_self s.card)
      · apply lt_of_le_of_lt (show (C c*q).degree ≤ q.degree from by
            rw [← Polynomial.smul_eq_C_mul]; exact Polynomial.degree_smul_le c q)
        exact lt_of_le_of_lt hqdeg (by exact_mod_cast Nat.lt_succ_self s.card)
    · intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,hqeval]
        linear_combination -hc
      · simp [heval i hi,hqzero i hi]

end PolynomialVacuumInterpolation

end OAI
