import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.BoxNonneg

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
open Finset MeasureTheory
lemma box_mono {H K : ℝ} (h : H ≤ K) (x : ℝ) : box H x ≤ box K x := by
  by_cases hx : x∈Set.Ioc 0 H
  · have hxK : x∈Set.Ioc 0 K := ⟨hx.1,hx.2.trans h⟩
    simp [box,Set.indicator_of_mem hx,Set.indicator_of_mem hxK]
  · simp only [box,Set.indicator_of_notMem hx]
    exact box_nonneg K x
lemma box_width_l1 {H K : ℝ} (hH : 0 ≤ H) (hK : 0 ≤ K) :
    (∫x : ℝ,|box H x-box K x|)=|H-K| := by
  rcases le_total H K with h|h
  · have he : (fun x : ℝ=>|box H x-box K x|)=fun x=>box K x-box H x := by
      funext x
      rw [abs_of_nonpos (sub_nonpos.mpr (box_mono h x))]
      ring
    rw [he,integral_sub (box_integrable K) (box_integrable H),box_integral hK,
      box_integral hH,abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · have he : (fun x : ℝ=>|box H x-box K x|)=fun x=>box H x-box K x := by
      funext x
      exact abs_of_nonneg (sub_nonneg.mpr (box_mono h x))
    rw [he,integral_sub (box_integrable H) (box_integrable K),box_integral hH,
      box_integral hK,abs_of_nonneg (sub_nonneg.mpr h)]

def variableWindow {ι : Type*} (s : Finset ι) (a : ι→ℂ) (u W : ι→ℝ) (x : ℝ) : ℂ :=
  ∑n∈s,a n*(box (W n) (x-u n):ℂ)
lemma variableWindow_integrable {ι : Type*} (s : Finset ι) (a : ι→ℂ) (u W : ι→ℝ) :
    Integrable (variableWindow s a u W) := by
  apply integrable_finsetSum
  intro n hn
  exact ((box_integrable (W n)).comp_sub_right (u n)).ofReal.const_mul (a n)

lemma variableWindow_width_l1 {ι : Type*} (s : Finset ι) (a : ι→ℂ) (u W : ι→ℝ)
    {D : ℝ} (hD : 0 ≤ D) (hW : ∀n∈s,0 ≤ W n) :
    (∫x : ℝ,‖sharpWindow s a u D x-variableWindow s a u W x‖) ≤
      ∑n∈s,‖a n‖*|D-W n| := by
  have hi (n : ι) : Integrable (fun x : ℝ=>‖a n‖*|box D (x-u n)-box (W n) (x-u n)|) :=
    (((box_integrable D).sub (box_integrable (W n))).norm.comp_sub_right (u n)).const_mul _
  calc
    _ ≤ ∫x : ℝ,∑n∈s,‖a n‖*|box D (x-u n)-box (W n) (x-u n)| := by
      apply integral_mono ((sharpWindow_integrable s a u D).sub
        (variableWindow_integrable s a u W)).norm (integrable_finsetSum s (fun n hn=>hi n))
      intro x
      unfold sharpWindow variableWindow
      dsimp only [Pi.sub_apply]
      rw [← sum_sub_distrib]
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro n hn
      rw [← mul_sub,norm_mul,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    _ = ∑n∈s,‖a n‖*|D-W n| := by
      rw [integral_finsetSum s (fun n hn=>hi n)]
      apply sum_congr rfl
      intro n hn
      rw [MeasureTheory.integral_const_mul]
      congr 1
      calc
        _ = ∫x : ℝ,|box D x-box (W n) x| :=
          integral_sub_right_eq_self (fun x : ℝ=>|box D x-box (W n) x|) (u n)
        _ = _ := box_width_l1 hD (hW n hn)

lemma fixedWindow_l1_bound {ι : Type*} (s : Finset ι) (a : ι→ℂ) (u W : ι→ℝ)
    {D : ℝ} (hD : 0 ≤ D) (hW : ∀n∈s,0 ≤ W n) :
    (∫x : ℝ,‖sharpWindow s a u D x‖) ≤
      (∫x : ℝ,‖variableWindow s a u W x‖)+(∑n∈s,‖a n‖*|D-W n|) := by
  have hs := (sharpWindow_integrable s a u D)
  have hv := (variableWindow_integrable s a u W)
  have hh : (∫x : ℝ,‖sharpWindow s a u D x‖) ≤
      (∫x : ℝ,‖variableWindow s a u W x‖)+
      (∫x : ℝ,‖sharpWindow s a u D x-variableWindow s a u W x‖) := by
    have hi : Integrable (fun x : ℝ=>‖sharpWindow s a u D x-variableWindow s a u W x‖) := (hs.sub hv).norm
    rw [← integral_add hv.norm hi]
    apply integral_mono hs.norm (hv.norm.add (hs.sub hv).norm)
    intro x
    have hh := norm_add_le (variableWindow s a u W x)
      (sharpWindow s a u D x-variableWindow s a u W x)
    have he : variableWindow s a u W x+(sharpWindow s a u D x-variableWindow s a u W x)=sharpWindow s a u D x := by abel
    rw [he] at hh
    exact hh
  exact hh.trans (add_le_add le_rfl (variableWindow_width_l1 s a u W hD hW))

lemma log_box_physical {n y H : ℝ} (hn : 0 < n) (hy : 0 < y) :
    box H (Real.log y-Real.log n)=box (n*(Real.exp H-1)) (y-n) := by
  have h1 : 0 < Real.log y-Real.log n ↔ 0 < y-n := by
    rw [sub_pos,sub_pos,Real.log_lt_log_iff hn hy]
  have he : Real.exp (Real.log y-Real.log n)=y/n := by
    rw [Real.exp_sub,Real.exp_log hy,Real.exp_log hn]
  have h2 : Real.log y-Real.log n ≤ H ↔ y-n ≤ n*(Real.exp H-1) := by
    rw [← Real.exp_le_exp,he,div_le_iff₀ hn]
    constructor <;> intro hh <;> nlinarith only [hh]
  have hm : (Real.log y-Real.log n)∈Set.Ioc 0 H ↔
      (y-n)∈Set.Ioc 0 (n*(Real.exp H-1)) := by simp only [Set.mem_Ioc,h1,h2]
  unfold box
  by_cases h : Real.log y-Real.log n∈Set.Ioc 0 H
  · simp [Set.indicator_of_mem h,Set.indicator_of_mem (hm.mp h)]
  · simp [Set.indicator_of_notMem h,Set.indicator_of_notMem (mt hm.mpr h)]

lemma physicalWindow_eq_variable {ι : Type*} (s : Finset ι) (a : ι→ℂ) (u : ι→ℝ)
    (hu : ∀n∈s,0 < u n) (H : ℝ) {y : ℝ} (hy : 0 < y) :
    sharpWindow s a (fun n=>Real.log (u n)) H (Real.log y)=
      variableWindow s a u (fun n=>u n*(Real.exp H-1)) y := by
  apply sum_congr rfl
  intro n hn
  rw [log_box_physical (hu n hn) hy]

lemma physicalWindow_integral_eq {ι : Type*} (s : Finset ι) (a : ι→ℂ) (u : ι→ℝ)
    (hu : ∀n∈s,0 < u n) (H : ℝ) :
    (∫y in Set.Ioi (0:ℝ),‖sharpWindow s a (fun n=>Real.log (u n)) H (Real.log y)‖)=
      ∫y : ℝ,‖variableWindow s a u (fun n=>u n*(Real.exp H-1)) y‖ := by
  rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with y
  by_cases hy : 0 < y
  · rw [Set.indicator_of_mem (show y∈Set.Ioi (0:ℝ) from hy),physicalWindow_eq_variable s a u hu H hy]
  · rw [Set.indicator_of_notMem (show y∉Set.Ioi (0:ℝ) from hy)]
    have hz : variableWindow s a u (fun n=>u n*(Real.exp H-1)) y=0 := by
      apply sum_eq_zero
      intro n hn
      have hh : y-u n∉Set.Ioc 0 (u n*(Real.exp H-1)) := by
        intro hh
        linarith [hu n hn,hh.1]
      simp [box,Set.indicator_of_notMem hh]
    rw [hz,norm_zero]

end OrdinarySharpWindow

end

end OAI
