import OAI.Computability.MatchingCount.ArgRoutine

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial
namespace Poly

@[fun_prop] theorem intDivNat : Poly (fun z : ℤ×ℕ => z.1/(z.2:ℤ)) := by
  have h : Poly (fun z : ℤ×ℕ => if decide (z.2=0) then (0:ℤ) else
      if decide (z.1<0) then -(((z.1.natAbs-1)/z.2+1:ℕ):ℤ)
      else ((z.1.natAbs/z.2:ℕ):ℤ)) := by fun_prop
  exact h.congr (fun z => by
    by_cases hd : z.2=0
    · simp [hd]
    · have hp : (0:ℤ)<z.2 := by exact_mod_cast (Nat.pos_of_ne_zero hd)
      simp only [hd,decide_false,Bool.false_eq_true,ite_false,decide_eq_true_eq]
      by_cases ha : z.1<0
      · rw [ite_eq_left ha]
        change -(((z.1.natAbs-1)/z.2+1:ℕ):ℤ)=Int.ediv z.1 (z.2:ℤ)
        rw [Int.ediv_of_neg_of_pos ha hp]
        have ha' : 0<z.1.natAbs := Int.natAbs_pos.mpr (ne_of_lt ha)
        have habs : (z.1.natAbs:ℤ) = -z.1 := by omega
        rw [Nat.cast_add,Nat.cast_one,Int.natCast_ediv,Nat.cast_sub (by omega : 1≤z.1.natAbs),Nat.cast_one,habs]
      · rw [ite_eq_right ha,Int.natCast_ediv,Int.natAbs_of_nonneg (le_of_not_gt ha)])

end Poly

def cappedDouble (z : ℕ×ℕ) : ℕ×ℕ := (z.1,min z.1 (2*z.2))
lemma cappedDouble_bound (z : ℕ×ℕ) (k : ℕ) :
    (cappedDouble^[k] z).1=z.1 ∧ (cappedDouble^[k] z).2≤z.1+z.2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    constructor
    · exact ih.1
    · dsimp only [cappedDouble]
      rw [ih.1]
      exact (Nat.min_le_left _ _).trans (Nat.le_add_right _ _)

lemma cappedDouble_iterate (cap k : ℕ) :
    cappedDouble^[k] (cap,min cap 1)=(cap,min cap (2^k)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply',ih]
    simp only [cappedDouble,pow_succ]
    congr 1
    omega

namespace Poly

@[fun_prop] theorem pow2Capped : Poly (fun z : ℕ×ℕ => min z.1 (2^z.2)) := by
  have hs : Poly cappedDouble := by unfold cappedDouble; fun_prop
  have hi := boundedIterate cappedDouble hs (2*X) (by
    intro z j hj
    have hb := cappedDouble_bound z.2 j
    simp only [encode_prod,pairBits_length,encode_nat,unary_length,eval_mul,eval_ofNat,eval_X]
    omega)
  have h : Poly (fun z : ℕ×ℕ => (cappedDouble^[z.2] (z.1,min z.1 1)).2) := by fun_prop
  exact h.congr (fun z => by rw [cappedDouble_iterate])

end Poly
end BinaryMatching.StackCode
end

end OAI
