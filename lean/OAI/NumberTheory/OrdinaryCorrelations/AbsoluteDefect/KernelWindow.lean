import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.BoxNonneg
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Smooth

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset

namespace OrdinarySharpWindow
open MeasureTheory Finset

noncomputable def kernelWindow {ι : Type*} (s : Finset ι) (a : ι→ℂ) (u : ι→ℝ)
    (G : ℝ→ℝ) (x : ℝ) : ℂ := ∑n∈s,a n*(G (x-u n):ℂ)

lemma kernelWindow_integrable {ι : Type*} (s : Finset ι) (a : ι→ℂ) (u : ι→ℝ)
    {G : ℝ→ℝ} (hG : Integrable G) : Integrable (kernelWindow s a u G) := by
  unfold kernelWindow
  exact integrable_finsetSum s (fun n hn=>(hG.comp_sub_right (u n)).ofReal.const_mul (a n))

lemma kernel_box_integrable {G : ℝ→ℝ} (hG : Integrable G) (H c : ℝ) :
    Integrable (fun z : ℝ=>G z*box H (c-z)) := by
  apply hG.mul_bdd ((box_integrable H).comp_sub_left c).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs,abs_of_nonneg (box_nonneg _ _)]
  exact box_le_one _ _

lemma box_kernel_comm {G : ℝ→ℝ} (H x u : ℝ) :
    (∫z : ℝ,G z*box H (x-z-u))=(∫z : ℝ,box H z*G (x-z-u)) := by
  have ht := integral_sub_left_eq_self («μ»:=volume)
    (fun z : ℝ=>G z*box H (x-z-u)) (x-u)
  rw [←ht]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with z
  have he : x-(x-u-z)-u=z := by ring
  have he' : x-u-z=x-z-u := by ring
  rw [he,he',mul_comm]

lemma smooth_sharpWindow {ι : Type*} (s : Finset ι) (a : ι→ℂ) (u : ι→ℝ)
    {G : ℝ→ℝ} (hG : Integrable G) (H x : ℝ) :
    smooth G (sharpWindow s a u H) x = smooth (box H) (kernelWindow s a u G) x := by
  have he (n : ι) (z : ℝ) : x-z-u n=x-u n-z := by ring
  have hL (n : ι) : Integrable (fun z : ℝ=>(G z:ℂ)*(a n*(box H (x-z-u n):ℂ))) := by
    have hh : Integrable (fun z : ℝ=>a n*((G z*box H (x-u n-z):ℝ):ℂ)) :=
      (kernel_box_integrable hG H (x-u n)).ofReal.const_mul (a n)
    convert hh using 1
    ext z
    rw [he]
    push_cast
    ring
  have hR (n : ι) : Integrable (fun z : ℝ=>(box H z:ℂ)*(a n*(G (x-z-u n):ℂ))) := by
    have hh : Integrable (fun z : ℝ=>a n*((G (x-u n-z)*box H (x-u n-(x-u n-z)):ℝ):ℂ)) :=
      ((kernel_box_integrable hG H (x-u n)).comp_sub_left (x-u n)).ofReal.const_mul (a n)
    convert hh using 1
    ext z
    have he' : x-u n-(x-u n-z)=z := by ring
    rw [he']
    push_cast
    rw [he]
    ring
  unfold smooth sharpWindow kernelWindow
  simp_rw [mul_sum]
  rw [integral_finsetSum s (fun n hn=>hL n),integral_finsetSum s (fun n hn=>hR n)]
  apply sum_congr rfl
  intro n hn
  have hLL : (fun z : ℝ=>(G z:ℂ)*(a n*(box H (x-z-u n):ℂ))) =
      (fun z : ℝ=>a n*((G z*box H (x-z-u n):ℝ):ℂ)) := by
    ext z
    push_cast
    ring
  have hRR : (fun z : ℝ=>(box H z:ℂ)*(a n*(G (x-z-u n):ℂ))) =
      (fun z : ℝ=>a n*((box H z*G (x-z-u n):ℝ):ℂ)) := by
    ext z
    push_cast
    ring
  rw [hLL,hRR,MeasureTheory.integral_const_mul,MeasureTheory.integral_const_mul,
    integral_complex_ofReal,integral_complex_ofReal,
    box_kernel_comm]

theorem sharp_l1_le_kernel {ι : Type*} (s : Finset ι) (a : ι→ℂ) (u : ι→ℝ)
    {G : ℝ→ℝ} (hG : Integrable G) (hG0 : ∀z,0≤G z)
    (hG1 : Integrable (fun z : ℝ=>G z*|z|)) {H : ℝ} (hH : 0≤H) :
    (∫z : ℝ,G z)*(∫x : ℝ,‖sharpWindow s a u H x‖) ≤
      2*(∑n∈s,‖a n‖)*(∫z : ℝ,G z*|z|)+H*(∫x : ℝ,‖kernelWindow s a u G x‖) := by
  let V := sharpWindow s a u H
  have hV := sharpWindow_integrable s a u H
  have herr := smooth_error_l1 hG hG0 hG1 hV (K:=2*(∑n∈s,‖a n‖)) (by
    intro z
    convert sharpWindow_translation_l1 s a u H z using 1; ring)
  have hsm := smooth_l1_le (box_integrable H) (box_nonneg H) (kernelWindow_integrable s a u hG)
  rw [box_integral hH] at hsm
  have he : smooth G V=smooth (box H) (kernelWindow s a u G) := by
    ext x
    exact smooth_sharpWindow s a u hG H x
  have hi := integral_add
    ((hV.const_mul ((∫z : ℝ,G z : ℝ):ℂ)).sub (smooth_integrable hG hV)).norm
    (smooth_integrable hG hV).norm
  have hmass : 0≤∫z : ℝ,G z := integral_nonneg hG0
  calc
    _ = ∫x : ℝ,‖((∫z : ℝ,G z : ℝ):ℂ)*V x‖ := by
      simp_rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hmass]
      rw [MeasureTheory.integral_const_mul]
    _ ≤ ∫x : ℝ,‖((∫z : ℝ,G z : ℝ):ℂ)*V x-smooth G V x‖+‖smooth G V x‖ := by
      apply integral_mono (hV.const_mul _).norm
        (((hV.const_mul _).sub (smooth_integrable hG hV)).norm.add (smooth_integrable hG hV).norm)
      intro x
      dsimp only [Pi.sub_apply,Pi.add_apply]
      simpa only [add_comm] using (norm_le_insert' (((∫z : ℝ,G z : ℝ):ℂ)*V x) (smooth G V x))
    _ = _ := hi
    _ ≤ _ := by
      dsimp only [Pi.sub_apply]
      simp only [integral_complex_ofReal] at herr
      apply add_le_add herr
      rw [he]
      exact hsm

end OrdinarySharpWindow

end

end OAI
