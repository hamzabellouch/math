import Mathlib

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace SK.Analytic
section LogIntegralConvexity
variable {E Ω : Type} [AddCommGroup E] [Module ℝ E]
  [MeasurableSpace Ω]

theorem convexOn_log_integral_exp (μ : Measure Ω) [NeZero μ]
    (f : E → Ω → ℝ) (hi : ∀ x, Integrable (fun y => Real.exp (f x y)) μ)
    (hc : ∀ y, ConvexOn ℝ univ (fun x => f x y)) :
    ConvexOn ℝ univ (fun x => Real.log (∫ y, Real.exp (f x y) ∂μ)) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ z _ a b ha hb hab
  let X := ∫ y, Real.exp (f x y) ∂μ
  let Z := ∫ y, Real.exp (f z y) ∂μ
  have hX : 0 < X := integral_exp_pos (hi x)
  have hZ : 0 < Z := integral_exp_pos (hi z)
  let c := a*Real.log X+b*Real.log Z
  have hbnd : ∀ y, Real.exp (f (a • x+b • z) y) ≤
      Real.exp c*(a*(Real.exp (f x y)/X)+b*(Real.exp (f z y)/Z)) := by
    intro y
    have hfc := (hc y).2 (mem_univ x) (mem_univ z) ha hb hab
    simp only [smul_eq_mul] at hfc
    have he := convexOn_exp.2 (mem_univ (f x y-Real.log X))
      (mem_univ (f z y-Real.log Z)) ha hb hab
    simp only [smul_eq_mul] at he
    have hcmp : f (a • x+b • z) y-c ≤
        a*(f x y-Real.log X)+b*(f z y-Real.log Z) := by dsimp [c]; linarith
    have hpre := (Real.exp_le_exp.mpr hcmp).trans he
    rw [Real.exp_sub (f x y) (Real.log X), Real.exp_log hX,
      Real.exp_sub (f z y) (Real.log Z), Real.exp_log hZ] at hpre
    calc
      Real.exp (f (a • x+b • z) y) = Real.exp c * Real.exp (f (a • x+b • z) y-c) := by
        rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpre (Real.exp_pos _).le
  have hbint : Integrable (fun y => Real.exp c*(a*(Real.exp (f x y)/X)+
      b*(Real.exp (f z y)/Z))) μ :=
    (((hi x).div_const X).const_mul a |>.add (((hi z).div_const Z).const_mul b)).const_mul _
  have hh := integral_mono (hi (a • x+b • z)) hbint hbnd
  have hright : (∫ y, Real.exp c*(a*(Real.exp (f x y)/X)+
      b*(Real.exp (f z y)/Z)) ∂μ) = Real.exp c := by
    rw [integral_const_mul, integral_add (((hi x).div_const X).const_mul a)
      (((hi z).div_const Z).const_mul b), integral_const_mul, integral_const_mul,
      integral_div, integral_div]
    change Real.exp c*(a*(X/X)+b*(Z/Z)) = Real.exp c
    rw [div_self hX.ne', div_self hZ.ne', mul_one, mul_one, hab, mul_one]
  rw [hright] at hh
  have hp : 0 < ∫ y, Real.exp (f (a • x+b • z) y) ∂μ :=
    integral_exp_pos (hi _)
  change Real.log (∫ y, Real.exp (f (a • x+b • z) y) ∂μ) ≤ c
  apply Real.exp_le_exp.mp
  simpa only [Real.exp_log hp] using hh

end LogIntegralConvexity
end SK.Analytic

end
end
end
end
end
end

end OAI
