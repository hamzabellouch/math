import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.KernelWindow

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

theorem kernel_l1_concentration {ι : Type*} (s : Finset ι) (a : ι→ℂ) (u : ι→ℝ)
    {G : ℝ→ℝ} (hG : Integrable G) (hG0 : ∀z,0≤G z)
    (hG1 : Integrable (fun z : ℝ=>G z*|z|))
    (hE : Integrable (fun x : ℝ=>‖kernelWindow s a u G x‖^2))
    {c q : ℝ} (hcentres : ∀n∈s,c≤u n ∧ u n≤c+1) (hq : 0<q) :
    (∫x : ℝ,‖kernelWindow s a u G x‖)≤
      3*q+(∫x : ℝ,‖kernelWindow s a u G x‖^2)/(4*q)+
        (∑n∈s,‖a n‖)*(∫z : ℝ,G z*|z|) := by
  classical
  let I := Set.Icc (c-1) (c+2)
  let V := kernelWindow s a u G
  have hV : Integrable V := kernelWindow_integrable s a u hG
  have hIq : Integrable (I.indicator (fun _ : ℝ=>q)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr
      (integrableOn_const («μ»:=volume) (s:=I) (by simp [I]))
  have hmoment (n : ι) : Integrable (fun x : ℝ=>‖a n‖*(G (x-u n)*|x-u n|)) :=
    (hG1.comp_sub_right (u n)).const_mul _
  have ht (x : ℝ) : 0≤∑n∈s,‖a n‖*(G (x-u n)*|x-u n|) :=
    sum_nonneg (fun n hn=>mul_nonneg (norm_nonneg _) (mul_nonneg (hG0 _) (abs_nonneg _)))
  have hquad (x : ℝ) : ‖V x‖≤q+‖V x‖^2/(4*q) := by
    have h4 : 0<4*q := by positivity
    have hh : (‖V x‖-q)*(4*q)≤‖V x‖^2 := by nlinarith [sq_nonneg (‖V x‖-2*q)]
    have hh' := (le_div_iff₀ h4).mpr hh
    linarith
  have hp (x : ℝ) : ‖V x‖≤I.indicator (fun _=>q) x+‖V x‖^2/(4*q)+
      ∑n∈s,‖a n‖*(G (x-u n)*|x-u n|) := by
    by_cases hx : x∈I
    · rw [Set.indicator_of_mem hx]
      exact (hquad x).trans (le_add_of_nonneg_right (ht x))
    · rw [Set.indicator_of_notMem hx,zero_add]
      have hfar (n : ι) (hn : n∈s) : 1≤|x-u n| := by
        obtain ⟨hlo,hhi⟩ := hcentres n hn
        have hout : x<c-1 ∨ c+2<x := by
          simpa only [I,Set.mem_Icc,not_and_or,not_le] using hx
        rcases hout with hh|hh
        · have ht := neg_le_abs (x-u n)
          linarith
        · have ht := le_abs_self (x-u n)
          linarith
      have hn : ‖V x‖≤∑n∈s,‖a n‖*(G (x-u n)*|x-u n|) := by
        unfold V kernelWindow
        apply (norm_sum_le _ _).trans
        apply sum_le_sum
        intro n hn
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hG0 _)]
        have hh := mul_le_mul_of_nonneg_left (hfar n hn) (mul_nonneg (norm_nonneg (a n)) (hG0 (x-u n)))
        nlinarith only [hh]
      exact hn.trans (le_add_of_nonneg_left (div_nonneg (sq_nonneg _) (by positivity)))
  calc
    _ ≤ ∫x : ℝ,I.indicator (fun _=>q) x+‖V x‖^2/(4*q)+
        ∑n∈s,‖a n‖*(G (x-u n)*|x-u n|) :=
      integral_mono hV.norm ((hIq.add (hE.div_const _)).add
        (integrable_finsetSum s (fun n hn=>hmoment n))) hp
    _ = _ := by
      have hfirst := integral_add (hIq.add (hE.div_const (4*q)))
        (integrable_finsetSum s (fun n hn=>hmoment n))
      have hsecond := integral_add hIq (hE.div_const (4*q))
      dsimp only [Pi.add_apply] at hfirst hsecond
      change (∫x : ℝ,I.indicator (fun _=>q) x+‖kernelWindow s a u G x‖^2/(4*q)+
        ∑n∈s,‖a n‖*(G (x-u n)*|x-u n|)) = _
      rw [hfirst,hsecond,MeasureTheory.integral_div,integral_indicator_const _ measurableSet_Icc,
        integral_finsetSum s (fun n hn=>hmoment n)]
      have he (n : ι) : (∫x : ℝ,‖a n‖*(G (x-u n)*|x-u n|))=
          ‖a n‖*(∫z : ℝ,G z*|z|) := by
        rw [MeasureTheory.integral_const_mul]
        congr 1
        exact integral_sub_right_eq_self (fun z : ℝ=>G z*|z|) (u n)
      simp_rw [he]
      rw [←sum_mul]
      have hvol : volume.real I=3 := by
        simp [I,Real.volume_real_Icc]
        ring_nf
        norm_num
      rw [hvol,smul_eq_mul]

end OrdinarySharpWindow

end

end OAI
