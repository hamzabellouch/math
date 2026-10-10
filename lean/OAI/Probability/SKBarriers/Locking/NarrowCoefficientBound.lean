import Mathlib
import OAI.Probability.SKBarriers.Locking.NarrowCDFTrial

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem narrowCDFMean_bounds (β : ℝ) {α : ℝ → ℝ} (hm : Monotone α)
    (r : ℝ) {h θ : ℝ} (hh : 0<h) (hθ : 0≤θ) :
    narrowCDFMean β α r h θ∈Icc (β^2*θ*α r) (β^2*θ*α (r+h)) := by
  have hlo : (∫ z in r..r+h,α r)≤∫ z in r..r+h,α z := by
    apply intervalIntegral.integral_mono_on (show r≤r+h by linarith) intervalIntegrable_const hm.intervalIntegrable
    intro z hz; exact hm hz.1
  have hhi : (∫ z in r..r+h,α z)≤∫ z in r..r+h,α (r+h) := by
    apply intervalIntegral.integral_mono_on (show r≤r+h by linarith) hm.intervalIntegrable intervalIntegrable_const
    intro z hz; exact hm hz.2
  simp only [intervalIntegral.integral_const,add_sub_cancel_left,smul_eq_mul] at hlo hhi
  have hn : h≠0 := ne_of_gt hh
  have Hlo := mul_le_mul_of_nonneg_left hlo (show 0≤β^2*(θ/h) by positivity)
  have Hhi := mul_le_mul_of_nonneg_left hhi (show 0≤β^2*(θ/h) by positivity)
  constructor
  · convert Hlo using 1 <;> try simp only [narrowCDFMean]
    all_goals field_simp
  · convert Hhi using 1 <;> try simp only [narrowCDFMean]
    all_goals field_simp

def narrowCDFErrorConstant (β : ℝ) : ℝ := 10*β^4+3*β^2

theorem narrowCDFErrorConstant_nonneg (β : ℝ) : 0≤narrowCDFErrorConstant β := by
  dsimp only [narrowCDFErrorConstant]; positivity

theorem narrowTentError_bound {B μ a θ ω : ℝ} (hB : 0≤B) (hμ : 0≤μ) (hμB : μ≤B)
    (ha : a∈Icc (0:ℝ) 1) (hω : ω∈Icc (0:ℝ) 1) :
    narrowTentError μ (B*a) (B*θ) ω≤6*B^2*θ^2+4*B^2*ω := by
  have hBa0 : 0≤B*a := mul_nonneg hB ha.1
  have hBa : B*a≤B := by simpa only [mul_one] using mul_le_mul_of_nonneg_left ha.2 hB
  have hmB : μ*(B*a)≤B^2 := by nlinarith [mul_le_mul hBa hμB hμ hB]
  have hBa2 : (B*a)^2≤B^2 := by nlinarith [sq_nonneg (B-B*a)]
  have hω2 : ω^2≤ω := by nlinarith [hω.1,hω.2]
  have hq : (B*a*ω)^2≤B^2*ω := by
    calc
      _ = (B*a)^2*ω^2 := by ring
      _ ≤ B^2*ω^2 := mul_le_mul_of_nonneg_right hBa2 (sq_nonneg ω)
      _ ≤ _ := mul_le_mul_of_nonneg_left hω2 (sq_nonneg B)
  have hm := mul_le_mul_of_nonneg_right hmB hω.1
  have hb := mul_le_mul_of_nonneg_right hBa2 hω.1
  unfold narrowTentError
  nlinarith

theorem narrowCDFTrialCoefficient_le (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α) (r q : ℝ)
    {h a θ : ℝ} (hh : 0<h) (ha : 0≤a) (hθ : 0≤θ) (haθ : a+θ=1) :
    narrowCDFTrialCoefficient β α r h q a θ≤
      β^2*((2*a^2+θ^2)/h)*(scalarCDFSusceptibilityAverage β α q-(∫ x in q..1,α x))+
      2*a*narrowCDFMean β α r h θ*(β^2*scalarCDFJointSusceptibility β α r q-1)+
      narrowCDFErrorConstant β*((α (r+h)-α (r-h))+θ^2) := by
  let M := narrowCDFMean β α r h θ
  let ω := α (r+h)-α (r-h)
  have hM := narrowCDFMean_bounds β hm r hh hθ
  have hai : a∈Icc (0:ℝ) 1 := ⟨ha,by linarith⟩
  have hθ1 : θ≤1 := by linarith
  have hω : ω∈Icc (0:ℝ) 1 := ⟨sub_nonneg.mpr (hm (show r-h≤r+h by linarith)),by dsimp only [ω]; linarith [(hα (r+h)).2,(hα (r-h)).1]⟩
  have hω0 : 0≤ω := hω.1
  have hM0 : 0≤M := (mul_nonneg (mul_nonneg (sq_nonneg β) hθ) (hα r).1).trans hM.1
  have hθB : β^2*θ≤β^2 := by nlinarith [sq_nonneg β]
  have hMθ : M≤β^2*θ := hM.2.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (hα (r+h)).2 (mul_nonneg (sq_nonneg β) hθ))
  have hMB : M≤β^2 := hMθ.trans hθB
  have HErr' := narrowTentError_bound (B:=β^2) (θ:=θ) (sq_nonneg β) hM0 hMB hai hω
  have hdiff : M-β^2*θ*α r≤β^2*ω := by
    have hmL := hm (show r-h≤r by linarith)
    have hd0 : 0≤α (r+h)-α r := sub_nonneg.mpr (hm (by linarith : r≤r+h))
    calc
      _ ≤ β^2*θ*(α (r+h)-α r) := by dsimp only [M] at *; nlinarith [hM.2]
      _ ≤ β^2*θ*ω := mul_le_mul_of_nonneg_left (by dsimp only [ω]; linarith) (mul_nonneg (sq_nonneg β) hθ)
      _ ≤ β^2*ω := mul_le_mul_of_nonneg_right hθB hω.1
  have hc : 2*a*(M-β^2*θ*α r)≤2*β^2*ω := by
    have H := mul_le_mul_of_nonneg_left hdiff (show 0≤2*a by positivity)
    have H' := mul_le_mul_of_nonneg_left hai.2 (show 0≤2*β^2*ω by positivity)
    nlinarith
  have ha2 : a^2≤1 := by nlinarith [hai.1,hai.2]
  have hc2 : β^2*a^2*ω≤β^2*ω := by nlinarith [mul_le_mul_of_nonneg_left ha2 (show 0≤β^2*ω by positivity)]
  have hn : 0≤β^2*α r*θ^2 := by have := (hα r).1; positivity
  unfold narrowCDFTrialCoefficient narrowCDFErrorConstant
  change _≤_+2*a*M*(_-1)+(10*β^4+3*β^2)*(ω+θ^2)
  change narrowTentError M (β^2*a) (β^2*θ) ω≤_ at HErr'
  have hωβ := mul_nonneg (sq_nonneg (β^2)) hω0
  dsimp only [M,ω] at *
  nlinarith [mul_nonneg (sq_nonneg β) (sq_nonneg θ),mul_nonneg (sq_nonneg (β^2)) (sq_nonneg θ)]

end SK.Analytic

end
end

end OAI
