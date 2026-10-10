import Mathlib
import OAI.Analysis.BrownMeasure.LogDerivative
import OAI.Analysis.BrownMeasure.RootSeries

namespace OAI

noncomputable section
open Filter
open scoped Topology Ring
namespace BrownLog
variable {A : Type*} [CStarAlgebra A] [Nontrivial A]
local instance : IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint :=
  IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
variable (τ : A →L[ℝ] ℝ) (hτ : ∀a b,τ (a*b)=τ (b*a)) (hstar : ∀a,τ (star a)=τ a)

omit [Nontrivial A] in
include hτ hstar in
lemma trace_inverse_square_deriv (a d : A) (hu : IsUnit a) :
    τ ((star a*a)⁻¹ʳ*(star d*a+star a*d))=2*τ (a⁻¹ʳ*d) := by
  rw [Ring.inverse_mul (Or.inl hu.star),mul_add,map_add]
  have h1 : τ ((a⁻¹ʳ*(star a)⁻¹ʳ)*(star d*a))=τ (a⁻¹ʳ*d) := by
    rw [← mul_assoc,hτ _ a]
    rw [← mul_assoc,← mul_assoc,Ring.mul_inverse_cancel a hu,one_mul,Ring.inverse_star]
    rw [← star_mul,hstar,hτ]
  have h2 : (a⁻¹ʳ*(star a)⁻¹ʳ)*(star a*d)=a⁻¹ʳ*d := by
    calc
      _ = a⁻¹ʳ*((star a)⁻¹ʳ*star a)*d := by simp only [mul_assoc]
      _ = _ := by rw [Ring.inverse_mul_cancel _ hu.star,mul_one]
  rw [h1,h2]
  ring

omit [Nontrivial A] in
lemma trace_resolvent_mul_zero (S : A)
    (hQ : Tendsto (fun n:ℕ=>‖S^n‖^(1/(n:ℝ))) atTop (𝓝 0))
    (hzero : ∀n:ℕ,τ (S^(n+1))=0) (t : ℝ) : τ ((1-t•S)⁻¹ʳ*S)=0 := by
  have hs := summable_pow_of_root_tendsto (t•S) (norm_root_smul_tendsto S t hQ)
  rw [(inverse_one_sub_eq_tsum _ hs).2,← hs.tsum_mul_right,τ.map_tsum (hs.mul_right S)]
  have he (n : ℕ) : τ ((t•S)^n*S)=0 := by
    rw [smul_pow,smul_mul_assoc,← pow_succ,map_smul,hzero,smul_zero]
  simp_rw [he]
  exact tsum_zero

include hτ hstar in
lemma trace_log_square_one_sub_eq_zero (S : A)
    (hQ : Tendsto (fun n:ℕ=>‖S^n‖^(1/(n:ℝ))) atTop (𝓝 0))
    (hzero : ∀n:ℕ,τ (S^(n+1))=0) : τ (CFC.log (star (1-S)*(1-S)))=0 := by
  let a : ℝ → A := fun t=>1-t•S
  let b : ℝ → A := fun t=>star (a t)*a t
  let d : ℝ → A := fun t=>star (-S)*a t+star (a t)*(-S)
  have ha (t : ℝ) : HasDerivAt a (-S) t := by
    simpa only [a,id_eq,one_smul] using ((hasDerivAt_id t).smul_const S).const_sub (1:A)
  have hb (t : ℝ) : IsSelfAdjoint (b t) := by
    exact isSelfAdjoint_iff.mpr (by simp [b,star_mul])
  have hu (t : ℝ) : IsUnit (a t) :=
    (inverse_one_sub_eq_tsum _ (summable_pow_of_root_tendsto _ (norm_root_smul_tendsto S t hQ))).1
  have hp (t y : ℝ) (hy : y∈spectrum ℝ (b t)) : 0<y := by
    have hnn : 0≤y := spectrum_star_mul_self_nonneg y hy
    refine hnn.lt_of_ne ?_
    intro he
    have hn := spectrum.zero_notMem ℝ ((hu t).star.mul (hu t))
    exact hn (he ▸ hy)
  have hdf (t : ℝ) : HasDerivAt b (d t) t := (ha t).star.fun_mul (ha t)
  have hc : Continuous d := by
    have hca : Continuous a := continuous_const.sub (continuous_id.smul continuous_const)
    exact (continuous_const.mul hca).add (hca.star.mul continuous_const)
  have hd0 (t : ℝ) : HasDerivAt (fun t=>τ (CFC.log (b t))) 0 t := by
    have hd := trace_log_hasDerivAt τ hτ (x:=t) hb hp hdf hc.continuousAt
    have he : τ ((b t)⁻¹ʳ*d t)=0 := by
      rw [trace_inverse_square_deriv τ hτ hstar _ _ (hu t),mul_neg,map_neg]
      rw [trace_resolvent_mul_zero τ S hQ hzero t]
      ring
    rwa [he] at hd
  have he := is_const_of_deriv_eq_zero (fun t=>(hd0 t).differentiableAt) (fun t=>(hd0 t).deriv) (1:ℝ) 0
  simpa [b,a,CFC.log_one] using he
end BrownLog
end

end OAI
