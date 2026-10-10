import Mathlib
import OAI.Analysis.Commutator.FiniteCancellation

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure Replicas (M : VonNeumannAlgebra H) (r : H →L[ℂ] H) where
  a : ℕ → H →L[ℂ] H
  mem : ∀ n,a n∈M
  initial : ∀ n,star (a n)*a n=r
  cross : ∀ n m,n≠m → star (a n)*a m=0
  source : ∀ n,a n*r=a n

theorem nonfinite_replicas (M : VonNeumannAlgebra H) (hfin : ¬IsFiniteAlgebra M) :
    ∃ r,r∈M ∧ IsStarProjection r ∧ r≠0 ∧ Nonempty (Replicas M r) := by
  classical
  simp only [IsFiniteAlgebra,not_forall] at hfin
  obtain ⟨v,hvM,hvi,hvn⟩ := hfin
  have hq : IsStarProjection (v*star v) := by
    constructor
    · change (v*star v)*(v*star v)=v*star v
      calc
        _=v*(star v*v)*star v := by noncomm_ring
        _=v*star v := by rw [hvi,mul_one]
    · exact IsSelfAdjoint.mul_star_self v
  let r : H →L[ℂ] H := 1-v*star v
  have hr : IsStarProjection r := hq.one_sub
  have hrn : r≠0 := by
    intro h
    exact hvn (sub_eq_zero.mp h).symm
  have hsvr : star v*r=0 := by
    change star v*(1-v*star v)=0
    rw [mul_sub,mul_one,←mul_assoc,hvi,one_mul,sub_self]
  have hrvs : r*v=0 := by
    simpa only [star_mul,hr.isSelfAdjoint.star_eq,star_star,star_zero] using congrArg star hsvr
  have hwords (n m : ℕ) : star (v^n*r)*(v^m*r)=if n=m then r else 0 := by
    induction n generalizing m with
    | zero =>
      cases m with
      | zero => simpa [hr.isSelfAdjoint.star_eq] using hr.isIdempotentElem.eq
      | succ m =>
        simp only [pow_zero,one_mul,pow_succ',Nat.zero_ne_add_one,ite_false,hr.isSelfAdjoint.star_eq]
        rw [show r*(v*v^m*r)=(r*v)*(v^m*r) by noncomm_ring,hrvs,zero_mul]
    | succ n ih =>
      cases m with
      | zero =>
        simp only [pow_zero,one_mul,pow_succ',Nat.add_one_ne_zero,ite_false,star_mul]
        rw [show star r*(star (v^n)*star v)*r=star r*star (v^n)*(star v*r) by noncomm_ring,hsvr,mul_zero]
      | succ m =>
        rw [pow_succ',pow_succ',star_mul,star_mul]
        rw [show star r*(star (v^n)*star v)*(v*v^m*r)=star (v^n*r)*(star v*v)*(v^m*r) by
          rw [star_mul]; noncomm_ring,hvi,mul_one,ih]
        simp
  refine ⟨r,M.sub_mem M.one_mem (M.mul_mem hvM (M.star_mem' hvM)),hr,hrn,
    ⟨⟨fun n => v^n*r,?_,?_,?_,?_⟩⟩⟩
  · intro n
    exact M.mul_mem (M.pow_mem hvM n) (M.sub_mem M.one_mem (M.mul_mem hvM (M.star_mem' hvM)))
  · intro n
    simpa using hwords n n
  · intro n m hnm
    simpa only [ite_eq_right hnm] using hwords n m
  · intro n
    rw [mul_assoc,hr.isIdempotentElem.eq]

end Kadison.PartialIsometryOrder

end

end
end

end OAI
