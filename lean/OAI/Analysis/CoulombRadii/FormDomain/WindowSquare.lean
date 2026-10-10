import Mathlib

namespace OAI

section
section
open Set
open scoped SchwartzMap
noncomputable section
namespace NeutralAtom
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem schwartz_square_bounded_lipschitz (g : 𝓢(E,ℝ)) :
    ∃ B L : ℝ, 0 ≤ B ∧ 0 ≤ L ∧ (∀ x, |g x^2| ≤ B) ∧
      (∀ x v, |g x^2-g v^2| ≤ L*‖x-v‖) := by
  let M := SchwartzMap.seminorm ℝ 0 0 g
  let D := SchwartzMap.seminorm ℝ 0 0 (SchwartzMap.fderivCLM ℝ E ℝ g)
  have hM : 0 ≤ M := apply_nonneg _ _
  have hD : 0 ≤ D := apply_nonneg _ _
  have hm (x : E) : |g x| ≤ M := by simpa only [Real.norm_eq_abs] using g.norm_le_seminorm ℝ x
  have hd (x : E) : ‖fderiv ℝ g x‖ ≤ D :=
    (SchwartzMap.fderivCLM ℝ E ℝ g).norm_le_seminorm ℝ x
  have hl (x v : E) : |g x-g v| ≤ D*‖x-v‖ := by
    have hh := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := (g : E → ℝ)) (f' := fderiv ℝ g)
      (fun z (_ : z∈(univ : Set E)) => (g.hasFDerivAt z).hasFDerivWithinAt)
      (fun z _ => hd z) (convex_univ : Convex ℝ (univ : Set E)) (mem_univ v) (mem_univ x)
    simpa only [Real.norm_eq_abs] using hh
  refine ⟨M^2,2*M*D,sq_nonneg _,mul_nonneg (mul_nonneg (by norm_num) hM) hD,?_,?_⟩
  · intro x
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hm x) 2
  · intro x v
    have hsum : |g x+g v| ≤ 2*M := (abs_add_le _ _).trans (by linarith [hm x,hm v])
    rw [show g x^2-g v^2=(g x-g v)*(g x+g v) by ring,abs_mul]
    calc
      _ ≤ (D*‖x-v‖)*(2*M) := mul_le_mul (hl x v) hsum (abs_nonneg _) (mul_nonneg hD (norm_nonneg _))
      _ = _ := by ring
end NeutralAtom
end

end
end

end OAI
