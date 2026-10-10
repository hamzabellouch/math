import Mathlib
import OAI.Probability.SKGap.Stability.StableFields

namespace OAI

section
noncomputable section
namespace SKGap
open Real Set

lemma scalar_remainder_of_lipschitz_derivative {f f' : ℝ → ℝ} {L : ℝ}
    (hL : 0 ≤ L) (hd : ∀ x, HasDerivAt f (f' x) x)
    (hl : ∀ x y, |f' x-f' y| ≤ L*|x-y|) (x d : ℝ) :
    |f (x+d)-f x-f' x*d| ≤ L*d^2 := by
  let R : ℝ → ℝ := fun z => f z-f x-f' x*(z-x)
  have hder (z : ℝ) : HasDerivAt R (f' z-f' x) z := by
    dsimp [R]
    convert! ((hd z).sub_const (f x)).sub (((hasDerivAt_id z).sub_const x).const_mul (f' x)) using 1; simp
  have bnd (z : ℝ) (hz : z ∈ segment ℝ x (x+d)) : ‖f' z-f' x‖ ≤ L*|d| := by
    rw [Real.norm_eq_abs]
    apply (hl z x).trans
    apply mul_le_mul_of_nonneg_left _ hL
    simpa only [Real.norm_eq_abs,add_sub_cancel_left] using norm_sub_le_of_mem_segment hz
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z (_ : z ∈ segment ℝ x (x+d)) => (hder z).hasDerivWithinAt) bnd
    (convex_segment x (x+d)) (left_mem_segment ℝ x (x+d)) (right_mem_segment ℝ x (x+d))
  simpa only [R,sub_self,mul_zero,sub_zero,add_sub_cancel_left,Real.norm_eq_abs,
    mul_assoc,← pow_two,sq_abs] using hh

lemma tanh_lipschitz_abs (x y : ℝ) : |tanh x-tanh y| ≤ |x-y| := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z (_ : z ∈ (univ : Set ℝ)) => (hasDerivAt_tanh z).hasDerivWithinAt)
    (C := 1) (fun z _ => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (tanh_sq_lt_one z).le)]
      linarith [sq_nonneg (tanh z)]) convex_univ (mem_univ y) (mem_univ x)
  simpa only [Real.norm_eq_abs,one_mul] using hh

lemma scalar_variance_lipschitz_abs (x y : ℝ) :
    |(1-tanh x^2)-(1-tanh y^2)| ≤ 2*|x-y| := by
  have hsum : |tanh x+tanh y| ≤ 2 := (abs_add_le _ _).trans (by
    linarith [(abs_tanh_lt_one x).le,(abs_tanh_lt_one y).le])
  calc
    _ = |tanh x-tanh y| * |tanh x+tanh y| := by
      rw [show (1-tanh x^2)-(1-tanh y^2) = -((tanh x-tanh y)*(tanh x+tanh y)) by ring, abs_neg, abs_mul]
    _ ≤ |x-y| * 2 := mul_le_mul (tanh_lipschitz_abs x y) hsum (abs_nonneg _) (abs_nonneg _)
    _ = _ := mul_comm _ _

lemma tanh_scalar_remainder (x d : ℝ) :
    |tanh (x+d)-tanh x-(1-tanh x^2)*d| ≤ 2*d^2 :=
  scalar_remainder_of_lipschitz_derivative (by norm_num) hasDerivAt_tanh
    scalar_variance_lipschitz_abs x d

lemma scalar_variance_hasDeriv (x : ℝ) :
    HasDerivAt (fun z => 1-tanh z^2) (-2*tanh x*(1-tanh x^2)) x := by
  convert! (hasDerivAt_const x (1:ℝ)).sub ((hasDerivAt_tanh x).pow 2) using 1; ring

lemma scalar_variance_deriv_lipschitz_abs (x y : ℝ) :
    |(-2*tanh x*(1-tanh x^2))-(-2*tanh y*(1-tanh y^2))| ≤ 6*|x-y| := by
  have hu : |tanh x| ≤ 1 := (abs_tanh_lt_one x).le
  have hv : |1-tanh y^2| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr (tanh_sq_lt_one y).le)]
    linarith [sq_nonneg (tanh y)]
  calc
    _ = 2*|tanh x*((1-tanh x^2)-(1-tanh y^2))+
        (tanh x-tanh y)*(1-tanh y^2)| := by
      rw [show (-2*tanh x*(1-tanh x^2))-(-2*tanh y*(1-tanh y^2))=
        -(2*(tanh x*((1-tanh x^2)-(1-tanh y^2))+
        (tanh x-tanh y)*(1-tanh y^2))) by ring,abs_neg,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    _ ≤ 2*(|tanh x| * |(1-tanh x^2)-(1-tanh y^2)|+
        |tanh x-tanh y| * |1-tanh y^2|) := by gcongr; exact (abs_add_le _ _).trans_eq (by rw [abs_mul,abs_mul])
    _ ≤ 2*(1*(2*|x-y|)+|x-y| * 1) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact add_le_add (mul_le_mul hu (scalar_variance_lipschitz_abs x y) (abs_nonneg _) (by norm_num))
        (mul_le_mul (tanh_lipschitz_abs x y) hv (abs_nonneg _) (abs_nonneg _))
    _ = _ := by ring

lemma scalar_variance_remainder (x d : ℝ) :
    |(1-tanh (x+d)^2)-(1-tanh x^2)-(-2*tanh x*(1-tanh x^2))*d| ≤ 6*d^2 :=
  scalar_remainder_of_lipschitz_derivative (by norm_num) scalar_variance_hasDeriv
    scalar_variance_deriv_lipschitz_abs x d
end SKGap
end
end

end OAI
