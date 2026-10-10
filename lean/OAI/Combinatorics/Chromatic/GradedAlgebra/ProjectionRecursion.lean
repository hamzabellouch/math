import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.PowerSeriesSplit

namespace OAI

section
namespace ElementaryPositivity.PowerSeriesSplit
open PowerSeries
noncomputable section
variable {R : Type*} [Ring R]

lemma left_coeff_projection (Q : R →+ R) (S : Subring R)
    (hQ : ∀x,Q (Q x)=Q x) (hOne : Q 1=1)
    (hMem : ∀x∈S,Q x∈S)
    (hMul : ∀x∈S,∀y∈S,Q (x*y)=Q x*Q y)
    (f : PowerSeries R) (hf : constantCoeff f=1) (hS : ∀n,coeff n f∈S) (n : ℕ) :
    coeff n (leftFactor Q f)=Q (coeff n f) := by
  have hs:=factors_mem Q S hMem f hS
  cases n with
  | zero => simp only [coeff_zero_eq_constantCoeff_apply,left_constant,hf,hOne]
  | succ n =>
    conv_lhs => rw [leftFactor,coeff_mk,pairCoefficients]
    have hleft (k : ℕ) : coeff k (leftFactor Q f)=(pairCoefficients Q f k).1 := by simp only [leftFactor,coeff_mk]
    have hright (k : ℕ) : coeff k (rightFactor Q f)=(pairCoefficients Q f k).2 := by simp only [rightFactor,coeff_mk]
    simp only [←hleft,←hright]
    change Q (coeff (n+1) f-∑i : Fin n,
      coeff (i.val+1) (leftFactor Q f)*coeff (n-i.val) (rightFactor Q f))=Q (coeff (n+1) f)
    rw [map_sub,map_sum]
    suffices H : (∑i : Fin n,Q (coeff (i.val+1) (leftFactor Q f)*
        coeff (n-i.val) (rightFactor Q f)))=0 by rw [H,sub_zero]
    apply Finset.sum_eq_zero
    intro i hi
    rw [hMul _ (hs.1 (i.val+1)) _ (hs.2 (n-i.val))]
    have he : n-i.val=(n-i.val-1)+1 := by omega
    rw [he,right_killed Q hQ,mul_zero]
end
end ElementaryPositivity.PowerSeriesSplit

end

end OAI
