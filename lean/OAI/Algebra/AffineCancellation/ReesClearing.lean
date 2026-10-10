import OAI.Algebra.AffineCancellation.ReesReduction

namespace OAI

noncomputable section

namespace ComplexCancellation.Rees
open MvPolynomial LaurentPolynomial
lemma embedding_q : embedding q=T 1 := by simp [q,eval,values]
lemma q_nonzero : q ≠ 0 := by
  intro h
  have := congrArg embedding h
  rw [embedding_q,map_zero] at this
  exact (isUnit_T (R := A) 1).ne_zero this
lemma clear_coefficient (r : A) : c r ∈ Clearing.subalgebra embedding q := by
  obtain ⟨r,rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ _ r
  change c (aπ r) ∈ _
  induction r using MvPolynomial.induction_on with
  | C z =>
    refine ⟨0,algebraMap ℂ B z,?_⟩
    rw [pow_zero,one_mul]
    have ha : aπ (MvPolynomial.C z)=algebraMap ℂ A z := aπ.commutes z
    rw [ha,c.commutes,embedding.commutes]
  | add r s hr hs => rw [map_add,map_add]; exact add_mem hr hs
  | mul_X r i hr =>
    rw [map_mul,map_mul]
    apply mul_mem hr
    fin_cases i
    · refine ⟨0,q*π (X 1),?_⟩
      simp only [pow_zero,one_mul,map_mul,embedding_q,embedding_π,eval,aeval_X,
        values,Matrix.cons_val_zero,Matrix.cons_val_one,a]
      change c (aπ (X 0))=T 1*(c (aπ (X 0))*T (-1))
      rw [mul_left_comm (T 1 : L),← T_add]
      norm_num
    · refine ⟨0,π (X 2),?_⟩
      simp only [pow_zero,one_mul,embedding_π,eval,aeval_X,values,Matrix.cons_val,a]
      rfl
    · refine ⟨0,π (X 3),?_⟩
      simp only [pow_zero,one_mul,embedding_π,eval,aeval_X,values,Matrix.cons_val,a]
      rfl
    · refine ⟨2,π (X 4),?_⟩
      simp only [embedding_q,T_pow,embedding_π,eval,aeval_X,values,Matrix.cons_val,a]
      change T 2*c (aπ (X 3))=c (aπ (X 3))*T 2
      exact mul_comm (T 2 : L) (c (aπ (X 3)))
    · refine ⟨2,π (X 5),?_⟩
      simp only [embedding_q,T_pow,embedding_π,eval,aeval_X,values,Matrix.cons_val,a]
      change T 2*c (aπ (X 4))=c (aπ (X 4))*T 2
      exact mul_comm (T 2 : L) (c (aπ (X 4)))

lemma clear_T (n : ℤ) : (T n : L) ∈ Clearing.subalgebra embedding q := by
  obtain ⟨m,hm⟩ : ∃ m : ℕ, 0 ≤ (m : ℤ)+n := ⟨n.natAbs,by omega⟩
  refine ⟨m,q^((m : ℤ)+n).toNat,?_⟩
  rw [map_pow,embedding_q,T_pow,T_pow,← T_add]
  congr 1
  simp only [mul_one,Int.toNat_of_nonneg hm]
lemma clear_all (r : L) : ∃ n : ℕ, ∃ s : B, embedding q^n*r=embedding s := by
  change r ∈ Clearing.subalgebra embedding q
  induction r using LaurentPolynomial.induction_on' with
  | add r s hr hs => exact add_mem hr hs
  | C_mul_T n r => exact mul_mem (clear_coefficient r) (clear_T n)
lemma clear_order (r : L) (hr : r ≠ 0) :
    ∃ (i : ℤ) (s : B), red s ≠ 0 ∧ embedding s=T i*r := by
  obtain ⟨n,b,hb⟩ := clear_all r
  have hb0 : b ≠ 0 := by
    intro hz
    rw [hz,map_zero] at hb
    exact mul_ne_zero (pow_ne_zero n (by rw [embedding_q]; exact (isUnit_T _).ne_zero)) hr hb
  obtain ⟨m,s,hs,hbs⟩ := maximum_q_factor hb0
  refine ⟨(n:ℤ)-m,s,hs,?_⟩
  rw [hbs,map_mul,map_pow,embedding_q,T_pow,T_pow] at hb
  have he := congrArg (fun t : L => T (-(m:ℤ))*t) hb
  simp only [mul_one] at he
  have h₀ : T (-(m:ℤ))*(T (m:ℤ):L)=1 := by rw [← T_add]; simp
  rw [← mul_assoc (T (-(m:ℤ))) (T (m:ℤ)) (embedding s),h₀,one_mul] at he
  rw [← mul_assoc,← T_add] at he
  rw [show -(m:ℤ)+(n:ℤ)=(n:ℤ)-m by omega] at he
  exact he.symm
end ComplexCancellation.Rees

end

end OAI
