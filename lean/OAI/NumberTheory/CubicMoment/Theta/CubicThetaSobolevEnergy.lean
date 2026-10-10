import OAI.NumberTheory.CubicMoment.Theta.CubicThetaLocalRellich

namespace OAI

/-! The actual real and imaginary Sobolev vectors are bounded by the
complex Euclidean energy integral. This is the norm comparison needed
to apply the local compact inclusion to the automorphic energy. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment.LocalSobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

local instance sobolevEnergy_tangent_borel : MeasurableSpace CubicThetaTangent := borel CubicThetaTangent
local instance sobolevEnergy_tangent_borelSpace : BorelSpace CubicThetaTangent := ⟨rfl⟩

private lemma l2_norm_sq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u : Lp V 2 tangentBorelVolume) : ‖u‖^2=∫ x, ‖u x‖^2 ∂tangentBorelVolume := by
  calc
    _ = inner ℝ u u := (real_inner_self_eq_norm_sq u).symm
    _ = ∫ x, inner ℝ (u x) (u x) ∂tangentBorelVolume := L2.inner_def u u
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with x
      exact real_inner_self_eq_norm_sq (u x)

private lemma value_norm_sq (g : C1c (E:=CubicThetaTangent)) :
    ‖toL2 (μ:=tangentBorelVolume) g‖^2=∫ x, ‖(g:CubicThetaTangent → ℝ) x‖^2 ∂tangentBorelVolume := by
  rw [l2_norm_sq]
  apply integral_congr_ae
  filter_upwards [(memLp_of_mem_C1c (μ:=tangentBorelVolume) g.property).coeFn_toLp] with x hx
  change ‖((memLp_of_mem_C1c (μ:=tangentBorelVolume) g.property).toLp _) x‖^2=_
  rw [hx]

private lemma gradientL2_norm_sq (g : C1c (E:=CubicThetaTangent)) :
    ‖toL2Grad (μ:=tangentBorelVolume) g‖^2=∫ x, ‖grad (g:CubicThetaTangent → ℝ) x‖^2 ∂tangentBorelVolume := by
  rw [l2_norm_sq]
  apply integral_congr_ae
  filter_upwards [(memLp_grad_of_mem_C1c (μ:=tangentBorelVolume) g.property).coeFn_toLp] with x hx
  change ‖((memLp_grad_of_mem_C1c (μ:=tangentBorelVolume) g.property).toLp _) x‖^2=_
  rw [hx]

lemma four_norms_eq (f : ℂ × ℝ → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    ‖toL2 (μ:=tangentBorelVolume) (realTest f hf hc)‖^2+
      ‖toL2 (μ:=tangentBorelVolume) (imagTest f hf hc)‖^2+
      ‖toL2Grad (μ:=tangentBorelVolume) (realTest f hf hc)‖^2+
      ‖toL2Grad (μ:=tangentBorelVolume) (imagTest f hf hc)‖^2=
        ∫ y, ‖f y‖^2+cubicThetaFunctionEnergy f y := by
  let r := realTest f hf hc
  let i := imagTest f hf hc
  have hr := (memLp_of_mem_C1c (μ:=tangentBorelVolume) r.property).integrable_norm_pow (by norm_num)
  have hi := (memLp_of_mem_C1c (μ:=tangentBorelVolume) i.property).integrable_norm_pow (by norm_num)
  have hdr := (memLp_grad_of_mem_C1c (μ:=tangentBorelVolume) r.property).integrable_norm_pow (by norm_num)
  have hdi := (memLp_grad_of_mem_C1c (μ:=tangentBorelVolume) i.property).integrable_norm_pow (by norm_num)
  have h₁ := integral_add hr hi
  have h₂ := integral_add (hr.add hi) hdr
  have h₃ := integral_add ((hr.add hi).add hdr) hdi
  simp only [Pi.add_apply] at h₁ h₂ h₃
  rw [h₂,h₁] at h₃
  rw [value_norm_sq,value_norm_sq,gradientL2_norm_sq,gradientL2_norm_sq,← h₃]

  calc
    _ = ∫ u, ‖f (cubicThetaTangentCoordinates u)‖^2+
        cubicThetaFunctionEnergy f (cubicThetaTangentCoordinates u) ∂tangentBorelVolume := by
      apply integral_congr_ae
      filter_upwards with u
      have hg := LocalSobolev.gradient_norm_sq f hf hc u
      have hv : ‖(realTest f hf hc : CubicThetaTangent → ℝ) u‖^2+
          ‖(imagTest f hf hc : CubicThetaTangent → ℝ) u‖^2=
          ‖f (cubicThetaTangentCoordinates u)‖^2 := by
        simp only [realTest,imagTest,Real.norm_eq_abs,sq_abs,← Complex.normSq_eq_norm_sq,
          Complex.normSq_apply]
        ring
      linear_combination hv+hg
    _ = _ := tangentBorelVolume_integral (fun y => ‖f y‖^2+cubicThetaFunctionEnergy f y)

private lemma prod_norm_sq_le {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]
    (v : V) (w : W) : ‖(v,w)‖^2≤‖v‖^2+‖w‖^2 := by
  rw [Prod.norm_mk]
  rcases le_total ‖v‖ ‖w‖ with h | h
  · rw [max_eq_right h]
    nlinarith [sq_nonneg ‖v‖]
  · rw [max_eq_left h]
    nlinarith [sq_nonneg ‖w‖]

lemma sobolev_pair_norm_sq_le (f : ℂ × ℝ → ℂ) (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) :
    ‖(realH1 f hf hc,imagH1 f hf hc)‖^2≤∫ y, ‖f y‖^2+cubicThetaFunctionEnergy f y := by
  have hr : ‖realH1 f hf hc‖^2≤
      ‖toL2 (μ:=tangentBorelVolume) (realTest f hf hc)‖^2+
      ‖toL2Grad (μ:=tangentBorelVolume) (realTest f hf hc)‖^2 :=
    prod_norm_sq_le _ _
  have hi : ‖imagH1 f hf hc‖^2≤
      ‖toL2 (μ:=tangentBorelVolume) (imagTest f hf hc)‖^2+
      ‖toL2Grad (μ:=tangentBorelVolume) (imagTest f hf hc)‖^2 :=
    prod_norm_sq_le _ _
  have hp := prod_norm_sq_le (realH1 f hf hc) (imagH1 f hf hc)
  rw [← four_norms_eq f hf hc]
  linarith

end CubicFirstMoment.LocalSobolev

end

end OAI
