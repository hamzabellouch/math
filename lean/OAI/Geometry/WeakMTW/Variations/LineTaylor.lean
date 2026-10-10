import Mathlib
import OAI.Geometry.WeakMTW.Variations.SecondCurveChain

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology ContDiff
namespace MovingTaylor
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem line_second_at {f : E → ℝ} (x v : E) (t : ℝ)
    (hf : ContDiffAt ℝ 2 f (x+t•v)) :
    deriv (deriv (fun r : ℝ => f (x+r•v))) t =
      fderiv ℝ (fderiv ℝ f) (x+t•v) v v := by
  have hv : ∀ r : ℝ, HasDerivAt (fun r : ℝ => x+r•v) v r := fun r => by
    simpa using (hasDerivAt_id r).smul_const v |>.const_add x
  have ha : HasDerivAt (deriv (fun r : ℝ => x+r•v)) 0 t := by
    have he : deriv (fun r : ℝ => x+r•v) = fun _ => v := funext (fun r => (hv r).deriv)
    rw [he]
    exact hasDerivAt_const t v
  simpa only [Function.comp_def,map_zero,add_zero] using
    SecondCurveChain.second hf (by fun_prop) (hv t) ha

 theorem second_segment {f : E → ℝ} (x v : E)
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 2 f (x+t•v)) :
    ∃ t ∈ Ioo (0 : ℝ) 1,
      f (x+v)-f x-fderiv ℝ f x v =
        fderiv ℝ (fderiv ℝ f) (x+t•v) v v / 2 := by
  let g : ℝ → ℝ := fun t => f (x+t•v)
  have hg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ 2 g t :=
    (hf t ht).comp t (by fun_prop)
  have hgOn : ContDiffOn ℝ (1+1 : ℕ) g (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact fun t ht => (hg t ht).contDiffWithinAt
  obtain ⟨t,ht,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 1)
    (by norm_num : (0 : ℝ) ≠ 1) hgOn
  have ht' : t ∈ Ioo (0 : ℝ) 1 := by simpa [uIoo_of_lt (by norm_num : (0 : ℝ) < 1)] using ht
  have hD : derivWithin g (uIcc (0 : ℝ) 1) 0 = fderiv ℝ f x v := by
    have hfx : ContDiffAt ℝ 2 f x := by simpa using hf 0 (by simp)
    have hfx' : HasFDerivAt f (fderiv ℝ f x) (x+(0 : ℝ)•v) := by simpa using (hfx.differentiableAt (by norm_num)).hasFDerivAt
    have hd := hfx'.comp_hasDerivAt 0
      (show HasDerivAt (fun r : ℝ => x+r•v) v 0 by simpa using (hasDerivAt_id (0 : ℝ)).smul_const v |>.const_add x)
    have hd' : HasDerivAt g (fderiv ℝ f x v) 0 := by simpa only [g,Function.comp_def] using hd
    exact hd'.hasDerivWithinAt.derivWithin (uniqueDiffOn_uIcc (by norm_num : (0 : ℝ) ≠ 1) 0 (by simp))
  have h2 : iteratedDeriv 2 g t = fderiv ℝ (fderiv ℝ f) (x+t•v) v v := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero,Function.comp_def,g] using
      line_second_at x v t (hf t ⟨ht'.1.le,ht'.2.le⟩)
  refine ⟨t,ht',?_⟩
  simp only [taylorWithinEval_succ,taylor_within_zero_eval,iteratedDerivWithin_succ,
    iteratedDerivWithin_zero] at he
  rw [hD] at he
  norm_num only [Nat.factorial_one,Nat.cast_one,inv_one,sub_zero,one_pow,one_mul,
    one_smul,Nat.factorial_succ,Nat.cast_mul,Nat.cast_ofNat] at he
  rw [h2,mul_one] at he
  simpa only [g,one_smul,zero_smul,add_zero,sub_add_eq_sub_sub] using he
end MovingTaylor
end

end WeakMTWGlobalSupport

end OAI
