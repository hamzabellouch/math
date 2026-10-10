import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace OAI

/-! # The two-term log-sum-exp inequality under a probability measure -/

open Set MeasureTheory
noncomputable section
namespace RegularPointCoordinates

theorem log_sum_exp_support (x y a b : ℝ) :
    Real.log (Real.exp a+Real.exp b)+
      (Real.exp a/(Real.exp a+Real.exp b))*(x-a)+
      (Real.exp b/(Real.exp a+Real.exp b))*(y-b) ≤
    Real.log (Real.exp x+Real.exp y) := by
  let S := Real.exp a+Real.exp b
  let p := Real.exp a/S
  let q := Real.exp b/S
  have hS : 0 < S := add_pos (Real.exp_pos _) (Real.exp_pos _)
  have hp : 0 ≤ p := (div_pos (Real.exp_pos _) hS).le
  have hq : 0 ≤ q := (div_pos (Real.exp_pos _) hS).le
  have hpq : p+q=1 := by dsimp only [p,q,S]; rw [←add_div,div_self hS.ne']
  have he := convexOn_exp.2 (mem_univ (x-a)) (mem_univ (y-b)) hp hq hpq
  simp only [smul_eq_mul] at he
  have hright : p*Real.exp (x-a)+q*Real.exp (y-b)=(Real.exp x+Real.exp y)/S := by
    dsimp only [p,q]
    rw [Real.exp_sub,Real.exp_sub]
    field_simp
  rw [hright] at he
  have hl := Real.log_le_log (Real.exp_pos _) he
  rw [Real.log_exp,Real.log_div (by positivity) hS.ne'] at hl
  change Real.log S+p*(x-a)+q*(y-b) ≤ _
  linarith

variable {Ω : Type*} [MeasurableSpace Ω]

theorem log_sum_exp_integral (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hlog : Integrable (fun x => Real.log (Real.exp (f x)+Real.exp (g x))) μ) :
    Real.log (Real.exp (∫ x, f x ∂μ)+Real.exp (∫ x, g x ∂μ)) ≤
      ∫ x, Real.log (Real.exp (f x)+Real.exp (g x)) ∂μ := by
  let a := ∫ x, f x ∂μ
  let b := ∫ x, g x ∂μ
  let S := Real.exp a+Real.exp b
  let p := Real.exp a/S
  let q := Real.exp b/S
  let H := fun x => Real.log S+p*(f x-a)+q*(g x-b)
  have hi : Integrable H μ :=
    ((integrable_const _).add ((hf.sub (integrable_const _)).const_mul p)).add
      ((hg.sub (integrable_const _)).const_mul q)
  have hf' : Integrable (fun x => p*(f x-a)) μ := (hf.sub (integrable_const a)).const_mul p
  have hg' : Integrable (fun x => q*(g x-b)) μ := (hg.sub (integrable_const b)).const_mul q
  have hc' : Integrable (fun _ : Ω => Real.log S) μ := integrable_const _
  have hs : (∫ x, H x ∂μ)=(∫ x, Real.log S+p*(f x-a) ∂μ)+(∫ x, q*(g x-b) ∂μ) :=
    integral_add (hc'.add hf') hg'
  have hs' : (∫ x, Real.log S+p*(f x-a) ∂μ)=
      (∫ _ : Ω, Real.log S ∂μ)+(∫ x, p*(f x-a) ∂μ) := integral_add hc' hf'
  have he : (∫ x, H x ∂μ)=Real.log S := by
    rw [hs,hs',integral_const_mul,integral_const_mul,
      integral_sub hf (integrable_const a),integral_sub hg (integrable_const b)]
    simp [a,b]
  rw [←he]
  apply integral_mono hi hlog
  intro x
  exact log_sum_exp_support (f x) (g x) a b

end RegularPointCoordinates

end

end OAI
