import OAI.NumberTheory.Ostmann.Conclusion.Scales
import OAI.NumberTheory.Ostmann.Construction.HalfListStatistic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
open Filter

theorem statistic_scale_lower {cψ cA g I : ℝ} {m X : ℕ}
    (hcψ : 0<cψ) (hcA : 0<cA) (hg : 0<g)
    (hlog : 0<Real.log (X:ℝ)) (hloglog : Real.log (Real.log (X:ℝ))≤2*(m:ℝ))
    (hconst : Real.exp (-(m:ℝ))≤cψ*cA*g^2) {N : ℝ}
    (hcard : cA*Real.sqrt X/Real.log (X:ℝ)^3 ≤ N)
    (hI : cψ*N*(Real.exp (-10*(m:ℝ))*g)^2≤I) :
    Real.sqrt X*Real.exp (-27*(m:ℝ))≤I := by
  have hden : 0<Real.log (X:ℝ)^3 := pow_pos hlog _
  have hdenupper : Real.log (X:ℝ)^3≤Real.exp (6*(m:ℝ)) := by
    have he : Real.log (X:ℝ)^3=Real.exp (3*Real.log (Real.log (X:ℝ))) := by
      simpa only [Nat.cast_ofNat,Real.exp_log hlog] using
        (Real.exp_nat_mul (Real.log (Real.log (X:ℝ))) 3).symm
    rw [he]
    exact Real.exp_le_exp.mpr (by linarith)
  have hexpsq : (Real.exp (-10*(m:ℝ)))^2=Real.exp (-20*(m:ℝ)) := by
    rw [pow_two,← Real.exp_add]; congr 1; ring
  have hexp : Real.exp (-27*(m:ℝ))=
      Real.exp (-(m:ℝ))*Real.exp (-20*(m:ℝ))/Real.exp (6*(m:ℝ)) := by
    rw [← Real.exp_add,← Real.exp_sub]; congr 1; ring
  calc
    _ = Real.sqrt X*(Real.exp (-(m:ℝ))*Real.exp (-20*(m:ℝ))/Real.exp (6*(m:ℝ))) := by rw [hexp]
    _ ≤ Real.sqrt X*((cψ*cA*g^2)*Real.exp (-20*(m:ℝ))/Real.exp (6*(m:ℝ))) := by
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hconst (Real.exp_pos _).le) (Real.exp_pos _).le) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt X*((cψ*cA*g^2)*Real.exp (-20*(m:ℝ))/Real.log (X:ℝ)^3) := by
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity) hden hdenupper)
        (Real.sqrt_nonneg _)
    _ = cψ*(cA*Real.sqrt X/Real.log (X:ℝ)^3)*(Real.exp (-10*(m:ℝ))*g)^2 := by
      rw [mul_pow,hexpsq]
      ring
    _ ≤ cψ*N*(Real.exp (-10*(m:ℝ))*g)^2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard hcψ.le) (sq_nonneg _)
    _ ≤ I := hI

theorem statistic_scale_conditions_eventually {k : ℕ} (hk : 0<k)
    {cψ cA g : ℝ} (hcψ : 0<cψ) (hcA : 0<cA) (hg : 0<g) :
    ∀ᶠ L : ℝ in atTop, L≤2*(Conclusion.bulkSize k L:ℝ) ∧
      Real.exp (-(Conclusion.bulkSize k L:ℝ))≤cψ*cA*g^2 := by
  have hz : 1≤Conclusion.bulkScale k := by
    unfold Conclusion.bulkScale
    apply one_le_pow₀
    exact_mod_cast (show 1≤k by omega)
  have hconst : ∀ᶠ L : ℝ in atTop,
      -Real.log (cψ*cA*g^2)≤(Conclusion.bulkSize k L:ℝ) :=
    (Conclusion.bulkSize_tendsto_atTop hk).eventually_ge_atTop _
  filter_upwards [hconst,eventually_ge_atTop (4:ℝ)] with L hc hL
  have hm := (Conclusion.bulkSize_bounds k (by linarith : 0≤L)).1
  have hml : L-2<(Conclusion.bulkSize k L:ℝ) := by nlinarith
  refine ⟨by linarith,?_⟩
  have he := Real.exp_le_exp.mpr (show -(Conclusion.bulkSize k L:ℝ)≤Real.log (cψ*cA*g^2) by linarith)
  rwa [Real.exp_log (by positivity)] at he

end Ostmann.Construction

end

end OAI
