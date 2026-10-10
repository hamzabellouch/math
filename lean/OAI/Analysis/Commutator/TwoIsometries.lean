import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison

section Isometries

variable {A : Type*} [Ring A] [StarRing A] (s t : A)
    (hs : star s*s=1) (ht : star t*t=1) (hst : star s*t=0)

include hs ht hst in
lemma two_isometries_words (n m : ℕ) :
    star (s^n*t)*(s^m*t)=if n=m then 1 else 0 := by
  classical
  have hts : star t*s=0 := by
    have he := congrArg star hst
    simpa only [star_mul,star_star,star_zero] using he
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => simpa using ht
    | succ m =>
      simp only [pow_zero,one_mul,pow_succ',Nat.zero_ne_add_one,ite_false]
      rw [show star t*(s*s^m*t)=(star t*s)*(s^m*t) by noncomm_ring,hts,zero_mul]
  | succ n ih =>
    cases m with
    | zero =>
      simp only [pow_zero,one_mul,pow_succ',Nat.add_one_ne_zero,ite_false,star_mul]
      rw [show star t*(star (s^n)*star s)*t=star t*star (s^n)*(star s*t) by noncomm_ring,hst,mul_zero]
    | succ m =>
      rw [pow_succ',pow_succ',star_mul,star_mul]
      rw [show star t*(star (s^n)*star s)*(s*s^m*t)=star (s^n*t)*(star s*s)*(s^m*t) by
        rw [star_mul]; noncomm_ring,hs,mul_one,ih]
      simp

include hs ht hst in
theorem two_isometries_finite_family (h : ℕ) :
    ∃ v : Fin h → A, ∀ i j, star (v i)*v j=if i=j then 1 else 0 := by
  classical
  refine ⟨fun i => s^i.val*t,?_⟩
  intro i j
  simpa only [Fin.val_inj] using two_isometries_words s t hs ht hst i.val j.val

end Isometries

end Kadison

end

end
end

end OAI
