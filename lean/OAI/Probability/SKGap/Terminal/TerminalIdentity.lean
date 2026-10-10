import Mathlib
import OAI.Probability.SKGap.Localization.ResidualInduction

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Primary
open Matrix
variable {n : ℕ}

lemma terminal_field_identity (j : ℝ) (J : Interaction n) (h : Fin n→ℝ)
    (k : ℕ) (x : Spin n) (i : Fin n) :
    fld j J h (k+1) x i-h i-J.mulVec (mag j J h (k+2) x) i+
        j*onsager j J h (k+1) x*mag j J h (k+2) x i =
      J.mulVec (residual j J h (k+1) x) i-
        j*onsager j J h (k+1) x*(residual j J h k x i+residual j J h (k+1) x i) := by
  rw [fld_eq]
  simp only [Nat.add_sub_cancel,residual,Matrix.mulVec,dotProduct,mul_sub,Finset.sum_sub_distrib]
  ring

theorem terminal_residual_identity (hn : 0<n) (j : ℝ) (J : Interaction n)
    (hJ : J.IsSymm) (h : Fin n→ℝ) (k : ℕ) (x : Spin n)
    (w y : Fin n→ℝ) (χ c : ℝ)
    (hy : ∀i,y i=J.mulVec w i-j*χ*w i-j*c*mag j J h (k+1) x i) :
    (∑i,(fld j J h (k+1) x i-h i-J.mulVec (mag j J h (k+2) x) i+
        j*onsager j J h (k+1) x*mag j J h (k+2) x i)*w i)-
        j*(onsager j J h (k+2) x-onsager j J h (k+1) x)*(n:ℝ)*c =
      (∑i,residual j J h (k+1) x i*y i)+
      j*(χ-onsager j J h (k+1) x)*(∑i,residual j J h (k+1) x i*w i)-
      j*onsager j J h (k+1) x*(∑i,residual j J h k x i*w i)-
      j*c*(∑i,residual j J h (k+1) x i*mag j J h (k+2) x i) := by
  have hsym:=mulVec_pair_symmetric J hJ (residual j J h (k+1) x) w
  have hinner:=residual_inner_product hn j J h (k+1) x
  have hfield : (∑i,residual j J h (k+1) x i*J.mulVec w i)=
      (∑i,residual j J h (k+1) x i*y i)+
      j*χ*(∑i,residual j J h (k+1) x i*w i)+
      j*c*(∑i,residual j J h (k+1) x i*mag j J h (k+1) x i) := by
    simp only [hy,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have ht : (∑i,(fld j J h (k+1) x i-h i-J.mulVec (mag j J h (k+2) x) i+
        j*onsager j J h (k+1) x*mag j J h (k+2) x i)*w i)=
      (∑i,residual j J h (k+1) x i*J.mulVec w i)-
      j*onsager j J h (k+1) x*(∑i,residual j J h k x i*w i)-
      j*onsager j J h (k+1) x*(∑i,residual j J h (k+1) x i*w i) := by
    simp_rw [terminal_field_identity]
    simp only [sub_mul,mul_add,add_mul,Finset.sum_sub_distrib,Finset.sum_add_distrib]
    rw [show (∑i,J.mulVec (residual j J h (k+1) x) i*w i)=
      ∑i,residual j J h (k+1) x i*J.mulVec w i from hsym]
    simp only [Finset.mul_sum]
    ring_nf
  rw [ht,hfield,hinner]
  ring

end SKGapCutoff.Primary

end
end

end OAI
