import Mathlib

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

namespace OrdinaryRieszPerron

def riesz (x : ℝ) : ℂ := (Ioc (0:ℝ) 1).indicator (fun t => (1:ℂ)-(t:ℂ)) x

def kernel (s : ℂ) : ℂ := 1/(s*(s+1))

lemma riesz_split (x : ℝ) : riesz x =
    (Ioc (0:ℝ) 1).indicator (fun _ => (1:ℂ)) x-
      (Ioc (0:ℝ) 1).indicator (fun t => (t:ℂ)^(1:ℂ)) x := by
  by_cases hx : x∈Ioc (0:ℝ) 1 <;> simp [riesz,hx]

lemma kernel_sub {s : ℂ} (hs : 0<s.re) : kernel s = 1/s-1/(s+1) := by
  have h0 : s≠0 := by intro hh; simp [hh] at hs
  have h1 : s+1≠0 := by intro hh; have := congrArg Complex.re hh; simp at this; linarith
  unfold kernel
  field_simp
  ring

lemma hasMellin_riesz {s : ℂ} (hs : 0<s.re) : HasMellin riesz s (kernel s) := by
  obtain ⟨hi1,he1⟩ := hasMellin_one_Ioc hs
  obtain ⟨hi2,he2⟩ := hasMellin_cpow_Ioc (1:ℂ) (s:=s) (by simp; linarith)
  constructor
  · unfold MellinConvergent at *
    have h := hi1.sub hi2
    change IntegrableOn (fun t : ℝ =>
      (t:ℂ)^(s-1) • ((Ioc (0:ℝ) 1).indicator (fun _ => (1:ℂ)) t) -
      (t:ℂ)^(s-1) • ((Ioc (0:ℝ) 1).indicator (fun t => (t:ℂ)^(1:ℂ)) t)) (Ioi 0) at h
    simpa only [riesz_split,smul_sub] using h
  · rw [kernel_sub hs,show riesz=(fun x => (Ioc (0:ℝ) 1).indicator (fun _ => (1:ℂ)) x-
        (Ioc (0:ℝ) 1).indicator (fun t => (t:ℂ)^(1:ℂ)) x) from funext riesz_split]
    simp only [mellin,smul_sub]
    rw [integral_sub hi1 hi2]
    exact congrArg₂ (·-·) he1 he2

lemma riesz_of_pos {x : ℝ} (hx : 0<x) : riesz x=(max (1-x) 0 : ℝ) := by
  by_cases hx1 : x≤1
  · simp [riesz,hx,hx1]
  · simp [riesz,hx,hx1,max_eq_right (by linarith : 1-x≤0)]

lemma continuousAt_riesz {x : ℝ} (hx : 0<x) : ContinuousAt riesz x := by
  apply ContinuousAt.congr (f:=fun x : ℝ => ((max (1-x) 0 : ℝ):ℂ))
  · fun_prop
  · filter_upwards [eventually_gt_nhds hx] with x hx
    exact (riesz_of_pos hx).symm

lemma kernel_norm_le {σ : ℝ} (hσ : 1≤σ) (t : ℝ) :
    ‖kernel ((σ:ℂ)+(t:ℂ)*Complex.I)‖ ≤ (1+t^2)⁻¹ := by
  let s : ℂ := (σ:ℂ)+(t:ℂ)*Complex.I
  have hsre : s.re=σ := by simp [s]
  have hsim : s.im=t := by simp [s]
  have hsq : ‖s‖^2=σ^2+t^2 := by rw [Complex.sq_norm]; simp [Complex.normSq_apply,hsre,hsim,pow_two]
  have hsq1 : ‖s+1‖^2=(σ+1)^2+t^2 := by rw [Complex.sq_norm]; simp [Complex.normSq_apply,hsre,hsim,pow_two]
  have hnn : ‖s‖≤‖s+1‖ := by nlinarith [norm_nonneg s,norm_nonneg (s+1)]
  have hden : 1+t^2≤‖s‖*‖s+1‖ := by
    nlinarith [mul_le_mul_of_nonneg_left hnn (norm_nonneg s)]
  change ‖kernel s‖≤_
  rw [kernel,norm_div,norm_one,norm_mul,one_div]
  exact (inv_le_inv₀ (lt_of_lt_of_le (by positivity : (0:ℝ)<1+t^2) hden)
    (by positivity : (0:ℝ)<1+t^2)).2 hden

lemma integrable_kernel {σ : ℝ} (hσ : 1≤σ) : Complex.VerticalIntegrable kernel σ := by
  apply Integrable.mono' integrable_inv_one_add_sq
  · apply Continuous.aestronglyMeasurable
    apply Continuous.div continuous_const
    · fun_prop
    · intro t
      apply mul_ne_zero
      · intro h
        have hh := congrArg Complex.re h
        simp at hh
        linarith
      · intro h
        have hh := congrArg Complex.re h
        simp at hh
        linarith
  · exact Filter.Eventually.of_forall (kernel_norm_le hσ)

theorem kernel_inverse {σ x : ℝ} (hσ : 1≤σ) (hx : 0<x) :
    mellinInv σ kernel x=riesz x := by
  have hs : 0<σ := by linarith
  have he (t : ℝ) : mellin riesz ((σ:ℂ)+(t:ℂ)*Complex.I)=kernel ((σ:ℂ)+(t:ℂ)*Complex.I) :=
    (hasMellin_riesz (by simpa using hs)).2
  have hi : Complex.VerticalIntegrable (mellin riesz) σ := by
    unfold Complex.VerticalIntegrable
    simpa only [Complex.VerticalIntegrable,he] using integrable_kernel hσ
  have hh := mellinInv_mellin_eq σ riesz hx (hasMellin_riesz (by simpa using hs)).1 hi (continuousAt_riesz hx)
  simpa only [mellinInv,he] using hh

end OrdinaryRieszPerron

end

end OAI
