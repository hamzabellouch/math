import OAI.Combinatorics.PolynomialVacuum.Algebra.Interpolation
import OAI.Combinatorics.PolynomialVacuum.Algebra.NodeFactors

namespace OAI

namespace PolynomialVacuumInterpolation
open MvPolynomial

 

theorem regular_lagrange_exists {ι : Type*} (s : Finset ι)
    (V : ι → MvPolynomial ι ℂ)
    (hcompat : ∀ i ∈ s, ∀ j ∈ s, mergeVariable i j (V i)=mergeVariable i j (V j)) :
    ∃ p : Polynomial (MvPolynomial ι ℂ),
      p.degree < (s.card : WithBot ℕ) ∧ ∀ i ∈ s, p.eval (X i)=V i := by
  apply integral_interpolation s X V
  · intro i _ j _ k _ hij hik hjk
    exact nodeFactor_isRelPrime hij hik hjk
  · intro i hi j hj
    change nodeFactor i j ∣ V i-V j
    rw [nodeFactor_dvd_iff,map_sub,sub_eq_zero]
    exact hcompat i hi j hj

theorem regular_lagrange_unique {ι : Type*} (s : Finset ι)
    (p r : Polynomial (MvPolynomial ι ℂ))
    (hp : p.degree < (s.card : WithBot ℕ)) (hr : r.degree < (s.card : WithBot ℕ))
    (heval : ∀ i ∈ s, p.eval (X i)=r.eval (X i)) : p=r := by
  exact Polynomial.eq_of_degrees_lt_of_eval_index_eq s MvPolynomial.X_injective.injOn hp hr heval

 

theorem divided_prescriptions_compatible {ι : Type*} (V W : ι → MvPolynomial ι ℂ)
    (hfactor : ∀ i, V i=X i*W i) {i j : ι}
    (h : mergeVariable i j (V i)=mergeVariable i j (V j)) :
    mergeVariable i j (W i)=mergeVariable i j (W j) := by
  classical
  by_cases hij : i=j
  · subst j; rfl
  rw [hfactor i,hfactor j,map_mul,map_mul] at h
  simp only [mergeVariable_X, ite_eq_right (Ne.symm hij)] at h
  exact mul_left_cancel₀ (MvPolynomial.X_ne_zero j) h

 

theorem zero_lagrange_exists {ι : Type*} (s : Finset ι)
    (V W : ι → MvPolynomial ι ℂ) (hfactor : ∀ i, V i=X i*W i)
    (hcompat : ∀ i ∈ s, ∀ j ∈ s, mergeVariable i j (V i)=mergeVariable i j (V j)) :
    ∃ p : Polynomial (MvPolynomial ι ℂ),
      p.degree ≤ (s.card : WithBot ℕ) ∧ p.eval 0=0 ∧ ∀ i ∈ s, p.eval (X i)=V i := by
  obtain ⟨p,hdeg,heval⟩ := regular_lagrange_exists s W
    (fun i hi j hj => divided_prescriptions_compatible V W hfactor (hcompat i hi j hj))
  refine ⟨Polynomial.X*p,?_,by simp,?_⟩
  · rw [mul_comm,Polynomial.degree_mul_X]
    by_cases hp : p=0
    · simp [hp]
    · rw [Polynomial.degree_eq_natDegree hp] at hdeg ⊢
      exact_mod_cast (Nat.succ_le_of_lt (WithBot.coe_lt_coe.mp hdeg))
  · intro i hi
    simp [Polynomial.eval_mul,heval i hi,hfactor i]

end PolynomialVacuumInterpolation

end OAI
